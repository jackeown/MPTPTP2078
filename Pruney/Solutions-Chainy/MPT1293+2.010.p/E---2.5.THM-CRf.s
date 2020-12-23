%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:52 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of clauses        :   35 (  48 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 237 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   1 average)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tops_2])).

fof(c_0_14,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))
      | k5_setfam_1(X28,X29) = k3_tarski(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_15,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_17,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1_0),esk3_0) = k3_tarski(esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk1_0),esk2_0) = k3_tarski(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_19])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k7_subset_1(X23,X24,X25) = k4_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_26,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26)))
      | m1_subset_1(k5_setfam_1(X26,X27),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_35,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(k4_xboole_0(X18,X19),X20)
      | r1_tarski(X18,k2_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_24]),c_0_19])])).

fof(c_0_38,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,k2_xboole_0(X16,X17))
      | r1_tarski(k4_xboole_0(X15,X16),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_37])])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_47,plain,(
    ! [X21,X22] : k3_tarski(k2_xboole_0(X21,X22)) = k2_xboole_0(k3_tarski(X21),k3_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

fof(c_0_48,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k4_xboole_0(X14,X13)) = k2_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_52,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk2_0),k2_xboole_0(k3_tarski(esk3_0),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k5_setfam_1(X1,X2) = k3_tarski(X2)
    | ~ r1_tarski(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_46])).

cnf(c_0_55,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(esk2_0),k3_tarski(k2_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57])]),c_0_52])).

cnf(c_0_60,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.027 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t6_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tops_2)).
% 0.14/0.39  fof(redefinition_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k5_setfam_1(X1,X2)=k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 0.14/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.39  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.14/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.14/0.39  fof(dt_k5_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k5_setfam_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 0.14/0.39  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.14/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.39  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.14/0.39  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.14/0.39  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.14/0.39  fof(t96_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 0.14/0.39  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.14/0.39  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k7_subset_1(u1_struct_0(X1),k5_setfam_1(u1_struct_0(X1),X2),k5_setfam_1(u1_struct_0(X1),X3)),k5_setfam_1(u1_struct_0(X1),k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3))))))), inference(assume_negation,[status(cth)],[t6_tops_2])).
% 0.14/0.39  fof(c_0_14, plain, ![X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k1_zfmisc_1(X28)))|k5_setfam_1(X28,X29)=k3_tarski(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).
% 0.14/0.39  fof(c_0_15, negated_conjecture, (l1_struct_0(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.14/0.39  fof(c_0_16, plain, ![X30, X31]:((~m1_subset_1(X30,k1_zfmisc_1(X31))|r1_tarski(X30,X31))&(~r1_tarski(X30,X31)|m1_subset_1(X30,k1_zfmisc_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.39  cnf(c_0_17, plain, (k5_setfam_1(X2,X1)=k3_tarski(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  fof(c_0_20, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.14/0.39  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k5_setfam_1(u1_struct_0(esk1_0),esk2_0),k5_setfam_1(u1_struct_0(esk1_0),esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (k5_setfam_1(u1_struct_0(esk1_0),esk3_0)=k3_tarski(esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (k5_setfam_1(u1_struct_0(esk1_0),esk2_0)=k3_tarski(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_19])).
% 0.14/0.39  fof(c_0_25, plain, ![X23, X24, X25]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k7_subset_1(X23,X24,X25)=k4_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.14/0.39  fof(c_0_26, plain, ![X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26)))|m1_subset_1(k5_setfam_1(X26,X27),k1_zfmisc_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_setfam_1])])).
% 0.14/0.39  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k7_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.14/0.39  cnf(c_0_30, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.39  cnf(c_0_31, plain, (m1_subset_1(k5_setfam_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.39  fof(c_0_33, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.14/0.39  fof(c_0_34, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.39  fof(c_0_35, plain, ![X18, X19, X20]:(~r1_tarski(k4_xboole_0(X18,X19),X20)|r1_tarski(X18,k2_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19])])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(k3_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_24]), c_0_19])])).
% 0.14/0.39  fof(c_0_38, plain, ![X15, X16, X17]:(~r1_tarski(X15,k2_xboole_0(X16,X17))|r1_tarski(k4_xboole_0(X15,X16),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_32])).
% 0.14/0.39  cnf(c_0_40, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.39  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  fof(c_0_43, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (~r1_tarski(k4_xboole_0(k3_tarski(esk2_0),k3_tarski(esk3_0)),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_30]), c_0_37])])).
% 0.14/0.39  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.39  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  fof(c_0_47, plain, ![X21, X22]:k3_tarski(k2_xboole_0(X21,X22))=k2_xboole_0(k3_tarski(X21),k3_tarski(X22)), inference(variable_rename,[status(thm)],[t96_zfmisc_1])).
% 0.14/0.39  fof(c_0_48, plain, ![X13, X14]:k2_xboole_0(X13,k4_xboole_0(X14,X13))=k2_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.39  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.14/0.39  cnf(c_0_51, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.14/0.39  cnf(c_0_52, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (~r1_tarski(k3_tarski(esk2_0),k2_xboole_0(k3_tarski(esk3_0),k5_setfam_1(u1_struct_0(esk1_0),k4_xboole_0(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.39  cnf(c_0_54, plain, (k5_setfam_1(X1,X2)=k3_tarski(X2)|~r1_tarski(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_46])).
% 0.14/0.39  cnf(c_0_55, plain, (k3_tarski(k2_xboole_0(X1,X2))=k2_xboole_0(k3_tarski(X1),k3_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.39  cnf(c_0_56, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.14/0.39  cnf(c_0_58, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (~r1_tarski(k3_tarski(esk2_0),k3_tarski(k2_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57])]), c_0_52])).
% 0.14/0.39  cnf(c_0_60, plain, (r1_tarski(k3_tarski(X1),k3_tarski(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_58, c_0_55])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 62
% 0.14/0.39  # Proof object clause steps            : 35
% 0.14/0.39  # Proof object formula steps           : 27
% 0.14/0.39  # Proof object conjectures             : 20
% 0.14/0.39  # Proof object clause conjectures      : 17
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 16
% 0.14/0.39  # Proof object initial formulas used   : 13
% 0.14/0.39  # Proof object generating inferences   : 16
% 0.14/0.39  # Proof object simplifying inferences  : 16
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 13
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 19
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 19
% 0.14/0.39  # Processed clauses                    : 248
% 0.14/0.39  # ...of these trivial                  : 6
% 0.14/0.39  # ...subsumed                          : 87
% 0.14/0.39  # ...remaining for further processing  : 155
% 0.14/0.39  # Other redundant clauses eliminated   : 2
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 2
% 0.14/0.39  # Generated clauses                    : 563
% 0.14/0.39  # ...of the previous two non-trivial   : 511
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 561
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 2
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 133
% 0.14/0.39  #    Positive orientable unit clauses  : 34
% 0.14/0.39  #    Positive unorientable unit clauses: 1
% 0.14/0.39  #    Negative unit clauses             : 19
% 0.14/0.39  #    Non-unit-clauses                  : 79
% 0.14/0.39  # Current number of unprocessed clauses: 298
% 0.14/0.39  # ...number of literals in the above   : 633
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 20
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 999
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 960
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 42
% 0.14/0.39  # Unit Clause-clause subsumption calls : 115
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 14
% 0.14/0.39  # BW rewrite match successes           : 4
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 8644
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.006 s
% 0.14/0.39  # Total time               : 0.045 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
