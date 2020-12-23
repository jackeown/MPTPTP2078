%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1402+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:14 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   27 (  50 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  251 ( 710 expanded)
%              Number of equality atoms :   27 (  85 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_2)).

fof(t44_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_pre_topc)).

fof(t32_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v4_pre_topc(k1_connsp_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_connsp_2)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X10,X11] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | X8 != k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(X10,X6)
        | ~ r2_hidden(X10,esk1_3(X6,X7,X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | X8 != k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( v4_pre_topc(X10,X6)
        | ~ r2_hidden(X10,esk1_3(X6,X7,X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | X8 != k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(X7,X10)
        | ~ r2_hidden(X10,esk1_3(X6,X7,X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | X8 != k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ v3_pre_topc(X10,X6)
        | ~ v4_pre_topc(X10,X6)
        | ~ r2_hidden(X7,X10)
        | r2_hidden(X10,esk1_3(X6,X7,X8))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | X8 != k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( k6_setfam_1(u1_struct_0(X6),esk1_3(X6,X7,X8)) = X8
        | X8 != k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_4(X6,X7,X8,X11),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | k6_setfam_1(u1_struct_0(X6),X11) != X8
        | X8 = k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r2_hidden(esk2_4(X6,X7,X8,X11),X11)
        | ~ v3_pre_topc(esk2_4(X6,X7,X8,X11),X6)
        | ~ v4_pre_topc(esk2_4(X6,X7,X8,X11),X6)
        | ~ r2_hidden(X7,esk2_4(X6,X7,X8,X11))
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | k6_setfam_1(u1_struct_0(X6),X11) != X8
        | X8 = k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk2_4(X6,X7,X8,X11),X6)
        | r2_hidden(esk2_4(X6,X7,X8,X11),X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | k6_setfam_1(u1_struct_0(X6),X11) != X8
        | X8 = k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( v4_pre_topc(esk2_4(X6,X7,X8,X11),X6)
        | r2_hidden(esk2_4(X6,X7,X8,X11),X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | k6_setfam_1(u1_struct_0(X6),X11) != X8
        | X8 = k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(X7,esk2_4(X6,X7,X8,X11))
        | r2_hidden(esk2_4(X6,X7,X8,X11),X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | k6_setfam_1(u1_struct_0(X6),X11) != X8
        | X8 = k1_connsp_2(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | v2_struct_0(X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).

fof(c_0_5,plain,(
    ! [X15,X16] :
      ( ( m1_subset_1(esk3_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X15),X16),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X15),X16),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ v4_pre_topc(esk3_2(X15,X16),X15)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X15),X16),X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).

cnf(c_0_6,plain,
    ( v4_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk1_3(X2,X3,X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk1_3(X2,X3,X4)),X1)
    | v4_pre_topc(esk3_2(X1,esk1_3(X2,X3,X4)),X2)
    | v2_struct_0(X2)
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(esk3_2(X1,esk1_3(X2,X3,X4)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk1_3(X2,X3,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk1_3(X1,X2,X3)),X1)
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(esk3_2(X1,esk1_3(X1,X2,X3)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v4_pre_topc(k1_connsp_2(X1,X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t32_connsp_2])).

cnf(c_0_14,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),esk1_3(X1,X2,X3)),X1)
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_10])).

cnf(c_0_15,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk1_3(X1,X2,X3)) = X3
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | m1_subset_1(k1_connsp_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ~ v4_pre_topc(k1_connsp_2(esk4_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

cnf(c_0_18,plain,
    ( v4_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | X1 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v4_pre_topc(k1_connsp_2(esk4_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( v4_pre_topc(k1_connsp_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),
    [proof]).

%------------------------------------------------------------------------------
