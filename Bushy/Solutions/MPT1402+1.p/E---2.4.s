%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : connsp_2__t32_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 160 expanded)
%              Number of clauses        :   28 (  62 expanded)
%              Number of leaves         :    7 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  282 (1716 expanded)
%              Number of equality atoms :   24 ( 188 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :  103 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/connsp_2__t32_connsp_2.p',d7_connsp_2)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t32_connsp_2.p',dt_k1_connsp_2)).

fof(t32_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v4_pre_topc(k1_connsp_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t32_connsp_2.p',t32_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/connsp_2__t32_connsp_2.p',t44_pre_topc)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t32_connsp_2.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t32_connsp_2.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/connsp_2__t32_connsp_2.p',t1_subset)).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X14,X15] :
      ( ( m1_subset_1(esk3_3(X10,X11,X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | X12 != k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_pre_topc(X14,X10)
        | ~ r2_hidden(X14,esk3_3(X10,X11,X12))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | X12 != k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v4_pre_topc(X14,X10)
        | ~ r2_hidden(X14,esk3_3(X10,X11,X12))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | X12 != k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(X11,X14)
        | ~ r2_hidden(X14,esk3_3(X10,X11,X12))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | X12 != k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ v3_pre_topc(X14,X10)
        | ~ v4_pre_topc(X14,X10)
        | ~ r2_hidden(X11,X14)
        | r2_hidden(X14,esk3_3(X10,X11,X12))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X10)))
        | X12 != k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( k6_setfam_1(u1_struct_0(X10),esk3_3(X10,X11,X12)) = X12
        | X12 != k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk4_4(X10,X11,X12,X15),k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | k6_setfam_1(u1_struct_0(X10),X15) != X12
        | X12 = k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(esk4_4(X10,X11,X12,X15),X15)
        | ~ v3_pre_topc(esk4_4(X10,X11,X12,X15),X10)
        | ~ v4_pre_topc(esk4_4(X10,X11,X12,X15),X10)
        | ~ r2_hidden(X11,esk4_4(X10,X11,X12,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | k6_setfam_1(u1_struct_0(X10),X15) != X12
        | X12 = k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v3_pre_topc(esk4_4(X10,X11,X12,X15),X10)
        | r2_hidden(esk4_4(X10,X11,X12,X15),X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | k6_setfam_1(u1_struct_0(X10),X15) != X12
        | X12 = k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( v4_pre_topc(esk4_4(X10,X11,X12,X15),X10)
        | r2_hidden(esk4_4(X10,X11,X12,X15),X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | k6_setfam_1(u1_struct_0(X10),X15) != X12
        | X12 = k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(X11,esk4_4(X10,X11,X12,X15))
        | r2_hidden(esk4_4(X10,X11,X12,X15),X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | k6_setfam_1(u1_struct_0(X10),X15) != X12
        | X12 = k1_connsp_2(X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | v2_struct_0(X10)
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_connsp_2])])])])])])).

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | m1_subset_1(k1_connsp_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v4_pre_topc(k1_connsp_2(X1,X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t32_connsp_2])).

fof(c_0_10,plain,(
    ! [X34,X35] :
      ( ( m1_subset_1(esk8_2(X34,X35),k1_zfmisc_1(u1_struct_0(X34)))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X34),X35),X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( r2_hidden(esk8_2(X34,X35),X35)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X34),X35),X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( ~ v4_pre_topc(esk8_2(X34,X35),X34)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(X34),X35),X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_pre_topc])])])])])).

cnf(c_0_11,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk3_3(X1,X2,X3)) = X3
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | X3 != k1_connsp_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ v4_pre_topc(k1_connsp_2(esk1_0,esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k6_setfam_1(u1_struct_0(X1),esk3_3(X1,X2,k1_connsp_2(X1,X2))) = k1_connsp_2(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk3_3(X1,X2,k1_connsp_2(X1,X2)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_12])).

cnf(c_0_18,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ v4_pre_topc(esk8_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( v4_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk3_3(X2,X3,X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k1_connsp_2(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk8_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_21,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_22,negated_conjecture,
    ( ~ v4_pre_topc(k1_connsp_2(esk1_0,esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(esk8_2(X1,esk3_3(X1,X2,k1_connsp_2(X1,X2))),esk3_3(X1,X2,k1_connsp_2(X1,X2)))
    | v4_pre_topc(k1_connsp_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( v4_pre_topc(k1_connsp_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v4_pre_topc(esk8_2(X1,esk3_3(X1,X2,k1_connsp_2(X1,X2))),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_17])).

cnf(c_0_29,plain,
    ( v4_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk3_3(X2,X3,k1_connsp_2(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_12])).

cnf(c_0_30,plain,
    ( v4_pre_topc(k1_connsp_2(X1,X2),X1)
    | m1_subset_1(esk8_2(X1,esk3_3(X1,X2,k1_connsp_2(X1,X2))),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_17])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk8_2(esk1_0,esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0))),esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

fof(c_0_33,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_34,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_35,plain,
    ( v4_pre_topc(k1_connsp_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(esk8_2(X1,esk3_3(X1,X2,k1_connsp_2(X1,X2))),esk3_3(X1,X3,k1_connsp_2(X1,X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk8_2(esk1_0,esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0))),esk3_3(esk1_0,X1,k1_connsp_2(esk1_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_35]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0)))
    | ~ m1_subset_1(X1,esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk8_2(esk1_0,esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0))),esk3_3(esk1_0,esk2_0,k1_connsp_2(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
