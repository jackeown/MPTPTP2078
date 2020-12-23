%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : compts_1__t33_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:51 EDT 2019

% Result     : Theorem 225.48s
% Output     : CNFRefutation 225.48s
% Verified   : 
% Statistics : Number of formulae       :   94 (49531 expanded)
%              Number of clauses        :   79 (21895 expanded)
%              Number of leaves         :    7 (11800 expanded)
%              Depth                    :   22
%              Number of atoms          :  387 (218115 expanded)
%              Number of equality atoms :   22 (16995 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   47 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_compts_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_compts_1(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',t33_compts_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',dt_u1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',dt_g1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',free_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',abstractness_v1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',d7_compts_1)).

fof(t32_compts_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_tops_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
        <=> ( v1_tops_2(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',t32_compts_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_compts_1(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ( v2_compts_1(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_compts_1])).

fof(c_0_8,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | m1_subset_1(u1_pre_topc(X19),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ( ~ v2_compts_1(esk2_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      | ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) )
    & ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | v2_compts_1(esk2_0,esk1_0) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | v2_compts_1(esk2_0,esk1_0) )
    & ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
    & ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
      | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X16,X17] :
      ( ( v1_pre_topc(g1_pre_topc(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( l1_pre_topc(g1_pre_topc(X16,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X26,X27,X28,X29] :
      ( ( X26 = X28
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) )
      & ( X27 = X29
        | g1_pre_topc(X26,X27) != g1_pre_topc(X28,X29)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k1_zfmisc_1(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_14,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | ~ v1_pre_topc(X7)
      | X7 = g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_15,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( u1_pre_topc(esk1_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_pre_topc(esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X10,X11,X12,X15] :
      ( ( m1_subset_1(esk3_3(X10,X11,X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ m1_setfam_1(X12,X11)
        | ~ v1_tops_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( r1_tarski(esk3_3(X10,X11,X12),X12)
        | ~ m1_setfam_1(X12,X11)
        | ~ v1_tops_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( m1_setfam_1(esk3_3(X10,X11,X12),X11)
        | ~ m1_setfam_1(X12,X11)
        | ~ v1_tops_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( v1_finset_1(esk3_3(X10,X11,X12))
        | ~ m1_setfam_1(X12,X11)
        | ~ v1_tops_2(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk4_2(X10,X11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( m1_setfam_1(esk4_2(X10,X11),X11)
        | v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( v1_tops_2(esk4_2(X10,X11),X10)
        | v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ r1_tarski(X15,esk4_2(X10,X11))
        | ~ m1_setfam_1(X15,X11)
        | ~ v1_finset_1(X15)
        | v2_compts_1(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_compts_1])])])])])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_pre_topc(esk1_0)) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_25])).

fof(c_0_29,plain,(
    ! [X34,X35] :
      ( ( v1_tops_2(X35,g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34)))
        | ~ v1_tops_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))))))
        | ~ v1_tops_2(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( v1_tops_2(X35,X34)
        | ~ v1_tops_2(X35,g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X34))))
        | ~ v1_tops_2(X35,g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X34),u1_pre_topc(X34))))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t32_compts_1])])])])])).

cnf(c_0_30,plain,
    ( v1_tops_2(esk4_2(X1,X2),X1)
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( m1_setfam_1(esk4_2(X1,X2),X2)
    | v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | v2_struct_0(X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( v1_tops_2(esk4_2(esk1_0,X1),esk1_0)
    | v2_compts_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_2(esk1_0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_compts_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_12])).

cnf(c_0_41,plain,
    ( v1_finset_1(esk3_3(X1,X2,X3))
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( m1_setfam_1(esk4_2(esk1_0,X1),X1)
    | v2_compts_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_tops_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_12]),c_0_36])]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_tops_2(esk4_2(esk1_0,esk2_0),esk1_0)
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_2(esk1_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v1_finset_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1,X2))
    | ~ v1_tops_2(X2,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_32]),c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( m1_setfam_1(esk4_2(esk1_0,esk2_0),esk2_0)
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( v1_tops_2(esk4_2(esk1_0,esk2_0),g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk3_3(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_51,plain,
    ( m1_setfam_1(esk3_3(X1,X2,X3),X2)
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_52,plain,
    ( r1_tarski(esk3_3(X1,X2,X3),X3)
    | ~ m1_setfam_1(X3,X2)
    | ~ v1_tops_2(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v2_compts_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_53,plain,
    ( v1_tops_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,plain,
    ( v2_compts_1(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,esk4_2(X2,X3))
    | ~ m1_setfam_1(X1,X3)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( v1_finset_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0,esk4_2(esk1_0,esk2_0)))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39])]),c_0_48]),c_0_45]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ v1_tops_2(X2,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_21]),c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( m1_setfam_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1,X2),X1)
    | ~ v1_tops_2(X2,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_21]),c_0_32]),c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1,X2),X2)
    | ~ v1_tops_2(X2,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_21]),c_0_32]),c_0_32])).

cnf(c_0_59,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_12]),c_0_36])]),c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_32]),c_0_21])])).

cnf(c_0_61,negated_conjecture,
    ( v1_tops_2(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1),g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_63,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0)
    | v2_compts_1(X1,X2)
    | ~ r1_tarski(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0,esk4_2(esk1_0,esk2_0)),esk4_2(X2,X1))
    | ~ m1_setfam_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0,esk4_2(esk1_0,esk2_0)),X1)
    | ~ m1_subset_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0,esk4_2(esk1_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0,esk4_2(esk1_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_47]),c_0_39])]),c_0_48]),c_0_45]),c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( m1_setfam_1(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0,esk4_2(esk1_0,esk2_0)),esk2_0)
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_47]),c_0_39])]),c_0_48]),c_0_45]),c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk3_3(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0,esk4_2(esk1_0,esk2_0)),esk4_2(esk1_0,esk2_0))
    | v2_compts_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_47]),c_0_39])]),c_0_48]),c_0_45]),c_0_49])).

cnf(c_0_67,negated_conjecture,
    ( v1_tops_2(X1,esk1_0)
    | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_32])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_39])).

cnf(c_0_69,negated_conjecture,
    ( v1_tops_2(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_39])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v2_compts_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_32])]),c_0_39])])).

cnf(c_0_71,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_63]),c_0_39]),c_0_12])]),c_0_64]),c_0_65]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( v1_tops_2(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),esk1_0)
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_74,negated_conjecture,
    ( m1_setfam_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1),X1)
    | v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_32])).

cnf(c_0_75,negated_conjecture,
    ( v1_finset_1(esk3_3(esk1_0,X1,X2))
    | ~ v1_tops_2(X2,esk1_0)
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_12])).

cnf(c_0_76,negated_conjecture,
    ( v1_tops_2(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[c_0_68,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( m1_setfam_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),esk2_0)
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_39])).

cnf(c_0_79,negated_conjecture,
    ( v1_finset_1(esk3_3(esk1_0,X1,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)))
    | ~ m1_setfam_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

cnf(c_0_80,negated_conjecture,
    ( m1_setfam_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[c_0_78,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ v1_tops_2(X2,esk1_0)
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_12])).

cnf(c_0_82,negated_conjecture,
    ( v1_finset_1(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_71]),c_0_80]),c_0_39])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,X1,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_setfam_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_72]),c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk3_3(esk1_0,X1,X2),X2)
    | ~ v1_tops_2(X2,esk1_0)
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_12])).

cnf(c_0_85,negated_conjecture,
    ( m1_setfam_1(esk3_3(esk1_0,X1,X2),X1)
    | ~ v1_tops_2(X2,esk1_0)
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_12])).

cnf(c_0_86,negated_conjecture,
    ( v2_compts_1(X1,X2)
    | ~ r1_tarski(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),esk4_2(X2,X1))
    | ~ m1_setfam_1(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),X1)
    | ~ m1_subset_1(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_71]),c_0_39])]),c_0_80])]),c_0_73])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk3_3(esk1_0,X1,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0))
    | v2_compts_1(esk2_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ m1_setfam_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_72]),c_0_68])).

cnf(c_0_89,negated_conjecture,
    ( m1_setfam_1(esk3_3(esk1_0,X1,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),X1)
    | ~ m1_setfam_1(esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v2_compts_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_76]),c_0_77])])).

cnf(c_0_90,negated_conjecture,
    ( v2_compts_1(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ r1_tarski(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X1))
    | ~ m1_setfam_1(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_21]),c_0_32]),c_0_32]),c_0_87])])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_71]),c_0_39])]),c_0_80])]),c_0_73])).

cnf(c_0_92,negated_conjecture,
    ( m1_setfam_1(esk3_3(esk1_0,esk2_0,esk4_2(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_71]),c_0_80]),c_0_39])])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_39]),c_0_91]),c_0_92])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
