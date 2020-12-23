%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1355+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:11 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 244 expanded)
%              Number of clauses        :   38 ( 101 expanded)
%              Number of leaves         :    6 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  285 (2014 expanded)
%              Number of equality atoms :    4 (  36 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   47 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & v1_tops_2(X2,X1)
                & ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ~ ( r1_tarski(X3,X2)
                        & m1_setfam_1(X3,u1_struct_0(X1))
                        & v1_finset_1(X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_compts_1)).

fof(d7_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_compts_1(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( m1_setfam_1(X3,X2)
                    & v1_tops_2(X3,X1)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                       => ~ ( r1_tarski(X4,X3)
                            & m1_setfam_1(X4,X2)
                            & v1_finset_1(X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_compts_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_k2_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(t10_compts_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(c_0_6,plain,(
    ! [X5,X6,X9] :
      ( ( m1_subset_1(esk1_2(X5,X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ m1_setfam_1(X6,u1_struct_0(X5))
        | ~ v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ v1_compts_1(X5)
        | ~ l1_pre_topc(X5) )
      & ( r1_tarski(esk1_2(X5,X6),X6)
        | ~ m1_setfam_1(X6,u1_struct_0(X5))
        | ~ v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ v1_compts_1(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_setfam_1(esk1_2(X5,X6),u1_struct_0(X5))
        | ~ m1_setfam_1(X6,u1_struct_0(X5))
        | ~ v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ v1_compts_1(X5)
        | ~ l1_pre_topc(X5) )
      & ( v1_finset_1(esk1_2(X5,X6))
        | ~ m1_setfam_1(X6,u1_struct_0(X5))
        | ~ v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ v1_compts_1(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk2_1(X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | v1_compts_1(X5)
        | ~ l1_pre_topc(X5) )
      & ( m1_setfam_1(esk2_1(X5),u1_struct_0(X5))
        | v1_compts_1(X5)
        | ~ l1_pre_topc(X5) )
      & ( v1_tops_2(esk2_1(X5),X5)
        | v1_compts_1(X5)
        | ~ l1_pre_topc(X5) )
      & ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ r1_tarski(X9,esk2_1(X5))
        | ~ m1_setfam_1(X9,u1_struct_0(X5))
        | ~ v1_finset_1(X9)
        | v1_compts_1(X5)
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_compts_1])])])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X16] :
      ( ( m1_subset_1(esk3_3(X11,X12,X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ m1_setfam_1(X13,X12)
        | ~ v1_tops_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( r1_tarski(esk3_3(X11,X12,X13),X13)
        | ~ m1_setfam_1(X13,X12)
        | ~ v1_tops_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( m1_setfam_1(esk3_3(X11,X12,X13),X12)
        | ~ m1_setfam_1(X13,X12)
        | ~ v1_tops_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( v1_finset_1(esk3_3(X11,X12,X13))
        | ~ m1_setfam_1(X13,X12)
        | ~ v1_tops_2(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk4_2(X11,X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( m1_setfam_1(esk4_2(X11,X12),X12)
        | v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( v1_tops_2(esk4_2(X11,X12),X11)
        | v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) )
      & ( ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X11))))
        | ~ r1_tarski(X16,esk4_2(X11,X12))
        | ~ m1_setfam_1(X16,X12)
        | ~ v1_finset_1(X16)
        | v2_compts_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_compts_1])])])])])).

fof(c_0_8,plain,(
    ! [X10] :
      ( ~ l1_struct_0(X10)
      | k2_struct_0(X10) = u1_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_9,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_10,plain,
    ( v1_compts_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,esk2_1(X2))
    | ~ m1_setfam_1(X1,u1_struct_0(X2))
    | ~ v1_finset_1(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(esk3_3(X1,X2,X3),X3)
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_finset_1(esk3_3(X1,X2,X3))
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X17] :
      ( ~ l1_struct_0(X17)
      | m1_subset_1(k2_struct_0(X17),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_struct_0])])).

cnf(c_0_14,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ( v1_compts_1(X1)
        <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t10_compts_1])).

cnf(c_0_17,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(X2,X3)
    | ~ v1_tops_2(esk2_1(X1),X3)
    | ~ m1_setfam_1(esk3_3(X3,X2,esk2_1(X1)),u1_struct_0(X1))
    | ~ m1_setfam_1(esk2_1(X1),X2)
    | ~ m1_subset_1(esk3_3(X3,X2,esk2_1(X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk2_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_18,plain,
    ( m1_setfam_1(esk3_3(X1,X2,X3),X2)
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( m1_setfam_1(esk2_1(X1),u1_struct_0(X1))
    | v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & ( ~ v1_compts_1(esk5_0)
      | ~ v2_compts_1(k2_struct_0(esk5_0),esk5_0) )
    & ( v1_compts_1(esk5_0)
      | v2_compts_1(k2_struct_0(esk5_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_23,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(u1_struct_0(X1),X2)
    | ~ v1_tops_2(esk2_1(X1),X2)
    | ~ m1_subset_1(esk3_3(X2,u1_struct_0(X1),esk2_1(X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(esk2_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_15])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,plain,
    ( v1_tops_2(esk2_1(X1),X1)
    | v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( v1_compts_1(esk5_0)
    | v2_compts_1(k2_struct_0(esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v2_compts_1(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,esk4_2(X2,X3))
    | ~ m1_setfam_1(X1,X3)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( r1_tarski(esk1_2(X1,X2),X2)
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_32,plain,
    ( v1_finset_1(esk1_2(X1,X2))
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_compts_1(esk5_0)
    | ~ v2_compts_1(k2_struct_0(esk5_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_19]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v2_compts_1(u1_struct_0(esk5_0),esk5_0)
    | v1_compts_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_29])])).

cnf(c_0_36,plain,
    ( v2_compts_1(X1,X2)
    | ~ v1_tops_2(esk4_2(X2,X1),X3)
    | ~ m1_setfam_1(esk1_2(X3,esk4_2(X2,X1)),X1)
    | ~ m1_setfam_1(esk4_2(X2,X1),u1_struct_0(X3))
    | ~ m1_subset_1(esk1_2(X3,esk4_2(X2,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(esk4_2(X2,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_compts_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,plain,
    ( v1_tops_2(esk4_2(X1,X2),X1)
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,plain,
    ( m1_setfam_1(esk4_2(X1,X2),X2)
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_compts_1(u1_struct_0(esk5_0),esk5_0)
    | ~ v1_compts_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_29])])).

cnf(c_0_42,negated_conjecture,
    ( v1_compts_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])])).

cnf(c_0_43,plain,
    ( v2_compts_1(X1,X2)
    | ~ m1_setfam_1(esk1_2(X2,esk4_2(X2,X1)),X1)
    | ~ m1_setfam_1(esk4_2(X2,X1),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_compts_1(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_44,plain,
    ( m1_setfam_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_setfam_1(X2,u1_struct_0(X1))
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | m1_subset_1(esk4_2(X1,u1_struct_0(X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_25])).

cnf(c_0_46,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | m1_setfam_1(esk4_2(X1,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_47,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | v1_tops_2(esk4_2(X1,u1_struct_0(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_compts_1(u1_struct_0(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_49,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | ~ v1_compts_1(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_25]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_42]),c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
