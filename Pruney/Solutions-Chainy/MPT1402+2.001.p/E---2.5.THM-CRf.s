%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  57 expanded)
%              Number of clauses        :   20 (  22 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  272 ( 858 expanded)
%              Number of equality atoms :   28 ( 106 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :  103 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k1_connsp_2(X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                    & ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X5,X4)
                        <=> ( v3_pre_topc(X5,X1)
                            & v4_pre_topc(X5,X1)
                            & r2_hidden(X2,X5) ) ) )
                    & k6_setfam_1(u1_struct_0(X1),X4) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(t29_tops_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_2)).

fof(t32_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v4_pre_topc(k1_connsp_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_connsp_2)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(c_0_5,plain,(
    ! [X12,X13,X14,X16,X17] :
      ( ( m1_subset_1(esk2_3(X12,X13,X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(X16,X12)
        | ~ r2_hidden(X16,esk2_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v4_pre_topc(X16,X12)
        | ~ r2_hidden(X16,esk2_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(X13,X16)
        | ~ r2_hidden(X16,esk2_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ v3_pre_topc(X16,X12)
        | ~ v4_pre_topc(X16,X12)
        | ~ r2_hidden(X13,X16)
        | r2_hidden(X16,esk2_3(X12,X13,X14))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( k6_setfam_1(u1_struct_0(X12),esk2_3(X12,X13,X14)) = X14
        | X14 != k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_4(X12,X13,X14,X17),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(esk3_4(X12,X13,X14,X17),X17)
        | ~ v3_pre_topc(esk3_4(X12,X13,X14,X17),X12)
        | ~ v4_pre_topc(esk3_4(X12,X13,X14,X17),X12)
        | ~ r2_hidden(X13,esk3_4(X12,X13,X14,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(esk3_4(X12,X13,X14,X17),X12)
        | r2_hidden(esk3_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( v4_pre_topc(esk3_4(X12,X13,X14,X17),X12)
        | r2_hidden(esk3_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(X13,esk3_4(X12,X13,X14,X17))
        | r2_hidden(esk3_4(X12,X13,X14,X17),X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | k6_setfam_1(u1_struct_0(X12),X17) != X14
        | X14 = k1_connsp_2(X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v2_tops_2(X7,X6)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X8,X7)
        | v4_pre_topc(X8,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_2(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
        | v2_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | v2_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) )
      & ( ~ v4_pre_topc(esk1_2(X6,X7),X6)
        | v2_tops_2(X7,X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_7,plain,
    ( v4_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk2_3(X2,X3,X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
      | ~ v2_tops_2(X11,X10)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X10),X11),X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_2])])])).

cnf(c_0_10,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | v4_pre_topc(esk1_2(X2,esk2_3(X1,X3,X4)),X1)
    | v2_tops_2(esk2_3(X1,X3,X4),X2)
    | X4 != k1_connsp_2(X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(X2,esk2_3(X1,X3,X4)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk2_3(X1,X3,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_tops_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk2_3(X1,X2,X3)) = X3
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_tops_2(esk2_3(X1,X2,X3),X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(X1,esk2_3(X1,X2,X3)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v4_pre_topc(k1_connsp_2(X1,X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t32_connsp_2])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | v4_pre_topc(X2,X1)
    | X2 != k1_connsp_2(X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_tops_2(esk2_3(X1,X3,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_12])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | v2_tops_2(esk2_3(X1,X2,X3),X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])).

fof(c_0_20,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | m1_subset_1(k1_connsp_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ v4_pre_topc(k1_connsp_2(esk4_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v4_pre_topc(X2,X1)
    | X2 != k1_connsp_2(X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ v4_pre_topc(k1_connsp_2(esk4_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | v4_pre_topc(k1_connsp_2(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d7_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=k1_connsp_2(X1,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))&![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X5,X4)<=>((v3_pre_topc(X5,X1)&v4_pre_topc(X5,X1))&r2_hidden(X2,X5)))))&k6_setfam_1(u1_struct_0(X1),X4)=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_connsp_2)).
% 0.13/0.38  fof(d2_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_2)).
% 0.13/0.38  fof(t29_tops_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)=>v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_2)).
% 0.13/0.38  fof(t32_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v4_pre_topc(k1_connsp_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_connsp_2)).
% 0.13/0.38  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.13/0.38  fof(c_0_5, plain, ![X12, X13, X14, X16, X17]:((((m1_subset_1(esk2_3(X12,X13,X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&((((v3_pre_topc(X16,X12)|~r2_hidden(X16,esk2_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(v4_pre_topc(X16,X12)|~r2_hidden(X16,esk2_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(r2_hidden(X13,X16)|~r2_hidden(X16,esk2_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(~v3_pre_topc(X16,X12)|~v4_pre_topc(X16,X12)|~r2_hidden(X13,X16)|r2_hidden(X16,esk2_3(X12,X13,X14))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X12)))|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))))&(k6_setfam_1(u1_struct_0(X12),esk2_3(X12,X13,X14))=X14|X14!=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&((m1_subset_1(esk3_4(X12,X13,X14,X17),k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&((~r2_hidden(esk3_4(X12,X13,X14,X17),X17)|(~v3_pre_topc(esk3_4(X12,X13,X14,X17),X12)|~v4_pre_topc(esk3_4(X12,X13,X14,X17),X12)|~r2_hidden(X13,esk3_4(X12,X13,X14,X17)))|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(((v3_pre_topc(esk3_4(X12,X13,X14,X17),X12)|r2_hidden(esk3_4(X12,X13,X14,X17),X17)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(v4_pre_topc(esk3_4(X12,X13,X14,X17),X12)|r2_hidden(esk3_4(X12,X13,X14,X17),X17)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))&(r2_hidden(X13,esk3_4(X12,X13,X14,X17))|r2_hidden(esk3_4(X12,X13,X14,X17),X17)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|k6_setfam_1(u1_struct_0(X12),X17)!=X14|X14=k1_connsp_2(X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).
% 0.13/0.38  fof(c_0_6, plain, ![X6, X7, X8]:((~v2_tops_2(X7,X6)|(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))|(~r2_hidden(X8,X7)|v4_pre_topc(X8,X6)))|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~l1_pre_topc(X6))&((m1_subset_1(esk1_2(X6,X7),k1_zfmisc_1(u1_struct_0(X6)))|v2_tops_2(X7,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~l1_pre_topc(X6))&((r2_hidden(esk1_2(X6,X7),X7)|v2_tops_2(X7,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~l1_pre_topc(X6))&(~v4_pre_topc(esk1_2(X6,X7),X6)|v2_tops_2(X7,X6)|~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~l1_pre_topc(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).
% 0.13/0.38  cnf(c_0_7, plain, (v4_pre_topc(X1,X2)|v2_struct_0(X2)|~r2_hidden(X1,esk2_3(X2,X3,X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|X4!=k1_connsp_2(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_8, plain, (r2_hidden(esk1_2(X1,X2),X2)|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_9, plain, ![X10, X11]:(~v2_pre_topc(X10)|~l1_pre_topc(X10)|(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|(~v2_tops_2(X11,X10)|v4_pre_topc(k6_setfam_1(u1_struct_0(X10),X11),X10)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_2])])])).
% 0.13/0.38  cnf(c_0_10, plain, (v2_tops_2(X2,X1)|~v4_pre_topc(esk1_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_11, plain, (v2_struct_0(X1)|v4_pre_topc(esk1_2(X2,esk2_3(X1,X3,X4)),X1)|v2_tops_2(esk2_3(X1,X3,X4),X2)|X4!=k1_connsp_2(X1,X3)|~v2_pre_topc(X1)|~m1_subset_1(esk1_2(X2,esk2_3(X1,X3,X4)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk2_3(X1,X3,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.13/0.38  cnf(c_0_12, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v2_struct_0(X1)|X3!=k1_connsp_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_13, plain, (v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~v2_tops_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_14, plain, (k6_setfam_1(u1_struct_0(X1),esk2_3(X1,X2,X3))=X3|v2_struct_0(X1)|X3!=k1_connsp_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_tops_2(esk2_3(X1,X2,X3),X1)|X3!=k1_connsp_2(X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(esk1_2(X1,esk2_3(X1,X2,X3)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v4_pre_topc(k1_connsp_2(X1,X2),X1)))), inference(assume_negation,[status(cth)],[t32_connsp_2])).
% 0.13/0.38  cnf(c_0_18, plain, (v2_struct_0(X1)|v4_pre_topc(X2,X1)|X2!=k1_connsp_2(X1,X3)|~v2_pre_topc(X1)|~v2_tops_2(esk2_3(X1,X3,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_12])).
% 0.13/0.38  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_tops_2(esk2_3(X1,X2,X3),X1)|X3!=k1_connsp_2(X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])).
% 0.13/0.38  fof(c_0_20, plain, ![X19, X20]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))|m1_subset_1(k1_connsp_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.13/0.38  fof(c_0_21, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&~v4_pre_topc(k1_connsp_2(esk4_0,esk5_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.13/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|v4_pre_topc(X2,X1)|X2!=k1_connsp_2(X1,X3)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_23, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (~v4_pre_topc(k1_connsp_2(esk4_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|v4_pre_topc(k1_connsp_2(X1,X2),X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 31
% 0.13/0.38  # Proof object clause steps            : 20
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 9
% 0.13/0.38  # Proof object clause conjectures      : 6
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 13
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 7
% 0.13/0.38  # Proof object simplifying inferences  : 9
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 22
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 22
% 0.13/0.38  # Processed clauses                    : 52
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 52
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 18
% 0.13/0.38  # ...of the previous two non-trivial   : 15
% 0.13/0.38  # Contextual simplify-reflections      : 4
% 0.13/0.38  # Paramodulations                      : 17
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 28
% 0.13/0.38  #    Positive orientable unit clauses  : 3
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 23
% 0.13/0.38  # Current number of unprocessed clauses: 7
% 0.13/0.38  # ...number of literals in the above   : 107
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 24
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 744
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 8
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 0
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4343
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.029 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
