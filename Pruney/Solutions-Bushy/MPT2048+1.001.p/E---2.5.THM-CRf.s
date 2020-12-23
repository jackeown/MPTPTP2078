%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:10 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   26 (  65 expanded)
%              Number of clauses        :   15 (  21 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  121 ( 325 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,X3))),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow19)).

fof(d2_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_yellow19(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                    & X3 = k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X4)),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow19)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,X3))),X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow19])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X9] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),u1_struct_0(X6))
        | ~ m1_yellow19(X7,X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5) )
      & ( X7 = k2_relset_1(u1_struct_0(k4_waybel_9(X5,X6,esk1_3(X5,X6,X7))),u1_struct_0(X5),u1_waybel_0(X5,k4_waybel_9(X5,X6,esk1_3(X5,X6,X7))))
        | ~ m1_yellow19(X7,X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5) )
      & ( ~ m1_subset_1(X9,u1_struct_0(X6))
        | X7 != k2_relset_1(u1_struct_0(k4_waybel_9(X5,X6,X9)),u1_struct_0(X5),u1_waybel_0(X5,k4_waybel_9(X5,X6,X9)))
        | m1_yellow19(X7,X5,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X6)
        | ~ l1_waybel_0(X6,X5)
        | v2_struct_0(X5)
        | ~ l1_struct_0(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_yellow19])])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_waybel_0(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),u1_waybel_0(esk2_0,k4_waybel_9(esk2_0,esk3_0,esk4_0))),esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( m1_yellow19(X3,X4,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != k2_relset_1(u1_struct_0(k4_waybel_9(X4,X2,X1)),u1_struct_0(X4),u1_waybel_0(X4,k4_waybel_9(X4,X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_waybel_0(X2,X4)
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),u1_waybel_0(esk2_0,k4_waybel_9(esk2_0,esk3_0,esk4_0))),esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,X3))),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(X1,X2,X3)),u1_struct_0(X1),u1_waybel_0(X1,k4_waybel_9(X1,X2,X3))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | m1_subset_1(k2_relset_1(X10,X11,X12),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_17,negated_conjecture,
    ( ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk2_0),u1_waybel_0(esk2_0,k4_waybel_9(esk2_0,esk3_0,esk4_0))),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_18,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ( v1_funct_1(u1_waybel_0(X16,X17))
        | ~ l1_struct_0(X16)
        | ~ l1_waybel_0(X17,X16) )
      & ( v1_funct_2(u1_waybel_0(X16,X17),u1_struct_0(X17),u1_struct_0(X16))
        | ~ l1_struct_0(X16)
        | ~ l1_waybel_0(X17,X16) )
      & ( m1_subset_1(u1_waybel_0(X16,X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16))))
        | ~ l1_struct_0(X16)
        | ~ l1_waybel_0(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_subset_1(u1_waybel_0(esk2_0,k4_waybel_9(esk2_0,esk3_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(esk2_0,esk3_0,esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X13,X14,X15] :
      ( ( v6_waybel_0(k4_waybel_9(X13,X14,X15),X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X14)) )
      & ( l1_waybel_0(k4_waybel_9(X13,X14,X15),X13)
        | v2_struct_0(X13)
        | ~ l1_struct_0(X13)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(X14,X13)
        | ~ m1_subset_1(X15,u1_struct_0(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ l1_waybel_0(k4_waybel_9(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_13])])).

cnf(c_0_24,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15]),
    [proof]).

%------------------------------------------------------------------------------
