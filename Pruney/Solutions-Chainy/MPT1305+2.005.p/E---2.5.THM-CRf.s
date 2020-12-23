%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:09 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  97 expanded)
%              Number of clauses        :   24 (  36 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 419 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( v2_tops_2(X2,X1)
                  & v2_tops_2(X3,X1) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tops_2)).

fof(t54_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => k7_setfam_1(X1,k4_subset_1(k1_zfmisc_1(X1),X2,X3)) = k4_subset_1(k1_zfmisc_1(X1),k7_setfam_1(X1,X2),k7_setfam_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_setfam_1)).

fof(t20_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( v1_tops_2(X2,X1)
                  & v1_tops_2(X3,X1) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tops_2)).

fof(t16_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( ( v2_tops_2(X2,X1)
                    & v2_tops_2(X3,X1) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tops_2])).

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))
      | k7_setfam_1(X9,k4_subset_1(k1_zfmisc_1(X9),X10,X11)) = k4_subset_1(k1_zfmisc_1(X9),k7_setfam_1(X9,X10),k7_setfam_1(X9,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_setfam_1])])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & v2_tops_2(esk2_0,esk1_0)
    & v2_tops_2(esk3_0,esk1_0)
    & ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X14,X15,X16] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
      | ~ v1_tops_2(X15,X14)
      | ~ v1_tops_2(X16,X14)
      | v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X14)),X15,X16),X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_tops_2])])])).

cnf(c_0_10,plain,
    ( k7_setfam_1(X2,k4_subset_1(k1_zfmisc_1(X2),X1,X3)) = k4_subset_1(k1_zfmisc_1(X2),k7_setfam_1(X2,X1),k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X12,X13] :
      ( ( ~ v2_tops_2(X13,X12)
        | v1_tops_2(k7_setfam_1(u1_struct_0(X12),X13),X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) )
      & ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X12),X13),X12)
        | v2_tops_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).

cnf(c_0_13,plain,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_tops_2(X2,X1)
    | ~ v1_tops_2(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),k7_setfam_1(u1_struct_0(esk1_0),X1),k7_setfam_1(u1_struct_0(esk1_0),esk3_0)) = k7_setfam_1(u1_struct_0(esk1_0),k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( v2_tops_2(X2,X1)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,X2),esk1_0)
    | ~ v1_tops_2(X2,esk1_0)
    | ~ v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k7_setfam_1(u1_struct_0(esk1_0),esk3_0)) = k7_setfam_1(u1_struct_0(esk1_0),k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v2_tops_2(X1,esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)),esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),X1),esk1_0)
    | ~ v2_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v2_tops_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_29,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X4))
      | m1_subset_1(k4_subset_1(X4,X5,X6),k1_zfmisc_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_28]),c_0_16])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_32,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))
      | m1_subset_1(k7_setfam_1(X7,X8),k1_zfmisc_1(k1_zfmisc_1(X7))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

cnf(c_0_33,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_11]),c_0_16])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_11])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:01:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 0.12/0.37  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t23_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v2_tops_2(X2,X1)&v2_tops_2(X3,X1))=>v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tops_2)).
% 0.12/0.37  fof(t54_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>k7_setfam_1(X1,k4_subset_1(k1_zfmisc_1(X1),X2,X3))=k4_subset_1(k1_zfmisc_1(X1),k7_setfam_1(X1,X2),k7_setfam_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_setfam_1)).
% 0.12/0.37  fof(t20_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v1_tops_2(X2,X1)&v1_tops_2(X3,X1))=>v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tops_2)).
% 0.12/0.37  fof(t16_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tops_2)).
% 0.12/0.37  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.12/0.37  fof(dt_k7_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v2_tops_2(X2,X1)&v2_tops_2(X3,X1))=>v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t23_tops_2])).
% 0.12/0.37  fof(c_0_7, plain, ![X9, X10, X11]:(~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9)))|(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(X9)))|k7_setfam_1(X9,k4_subset_1(k1_zfmisc_1(X9),X10,X11))=k4_subset_1(k1_zfmisc_1(X9),k7_setfam_1(X9,X10),k7_setfam_1(X9,X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_setfam_1])])])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))&((v2_tops_2(esk2_0,esk1_0)&v2_tops_2(esk3_0,esk1_0))&~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X14, X15, X16]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|(~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|(~v1_tops_2(X15,X14)|~v1_tops_2(X16,X14)|v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X14)),X15,X16),X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_tops_2])])])).
% 0.12/0.37  cnf(c_0_10, plain, (k7_setfam_1(X2,k4_subset_1(k1_zfmisc_1(X2),X1,X3))=k4_subset_1(k1_zfmisc_1(X2),k7_setfam_1(X2,X1),k7_setfam_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_12, plain, ![X12, X13]:((~v2_tops_2(X13,X12)|v1_tops_2(k7_setfam_1(u1_struct_0(X12),X13),X12)|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~l1_pre_topc(X12))&(~v1_tops_2(k7_setfam_1(u1_struct_0(X12),X13),X12)|v2_tops_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).
% 0.12/0.37  cnf(c_0_13, plain, (v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v1_tops_2(X2,X1)|~v1_tops_2(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),k7_setfam_1(u1_struct_0(esk1_0),X1),k7_setfam_1(u1_struct_0(esk1_0),esk3_0))=k7_setfam_1(u1_struct_0(esk1_0),k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_17, plain, (v2_tops_2(X2,X1)|~v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),X1,X2),esk1_0)|~v1_tops_2(X2,esk1_0)|~v1_tops_2(X1,esk1_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k7_setfam_1(u1_struct_0(esk1_0),esk3_0))=k7_setfam_1(u1_struct_0(esk1_0),k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (v2_tops_2(X1,esk1_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),X1),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0)),esk1_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_23, plain, (v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),esk1_0)|~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|~m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),X1),esk1_0)|~v2_tops_2(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_23, c_0_14])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (v2_tops_2(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (~v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)|~m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_11])])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (v2_tops_2(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_29, plain, ![X4, X5, X6]:(~m1_subset_1(X5,k1_zfmisc_1(X4))|~m1_subset_1(X6,k1_zfmisc_1(X4))|m1_subset_1(k4_subset_1(X4,X5,X6),k1_zfmisc_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (~m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk1_0)),esk2_0,esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_28]), c_0_16])])).
% 0.12/0.37  cnf(c_0_31, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  fof(c_0_32, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(X7)))|m1_subset_1(k7_setfam_1(X7,X8),k1_zfmisc_1(k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))|~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_11]), c_0_16])])).
% 0.12/0.37  cnf(c_0_34, plain, (m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (~m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_11])])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_16])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 37
% 0.12/0.37  # Proof object clause steps            : 24
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 21
% 0.12/0.37  # Proof object clause conjectures      : 18
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 12
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 12
% 0.12/0.37  # Proof object simplifying inferences  : 14
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 12
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 12
% 0.12/0.37  # Processed clauses                    : 78
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 78
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 8
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 258
% 0.19/0.37  # ...of the previous two non-trivial   : 256
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 258
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 58
% 0.19/0.37  #    Positive orientable unit clauses  : 17
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 39
% 0.19/0.37  # Current number of unprocessed clauses: 202
% 0.19/0.37  # ...number of literals in the above   : 590
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 20
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 244
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 204
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.37  # Unit Clause-clause subsumption calls : 69
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 68
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 14581
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
