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
% DateTime   : Thu Dec  3 11:19:18 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 735 expanded)
%              Number of clauses        :   66 ( 291 expanded)
%              Number of leaves         :   16 ( 181 expanded)
%              Depth                    :   14
%              Number of atoms          :  280 (3086 expanded)
%              Number of equality atoms :   55 ( 468 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & v1_tex_2(X2,X1) )
               => v1_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t5_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( u1_struct_0(X2) = u1_struct_0(X3)
               => g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tsep_1)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    & v1_tex_2(X2,X1) )
                 => v1_tex_2(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_tex_2])).

fof(c_0_17,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_tex_2(X28,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | X29 != u1_struct_0(X28)
        | v1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk1_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))
        | v1_tex_2(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( esk1_2(X27,X28) = u1_struct_0(X28)
        | v1_tex_2(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ v1_subset_1(esk1_2(X27,X28),u1_struct_0(X27))
        | v1_tex_2(X28,X27)
        | ~ m1_pre_topc(X28,X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_18,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | r1_tarski(u1_struct_0(X23),u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    & v1_tex_2(esk3_0,esk2_0)
    & ~ v1_tex_2(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | l1_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_21,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | ~ m1_pre_topc(X26,X24)
      | u1_struct_0(X25) != u1_struct_0(X26)
      | g1_pre_topc(u1_struct_0(X25),u1_pre_topc(X25)) = g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_tsep_1])])])).

fof(c_0_28,plain,(
    ! [X19,X20] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)),X19)
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | u1_struct_0(k1_pre_topc(X15,X16)) = X16 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_30,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_tex_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_33,plain,(
    ! [X31,X32] :
      ( ( ~ v1_subset_1(X32,X31)
        | X32 != X31
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) )
      & ( X32 = X31
        | v1_subset_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_36,plain,
    ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1)
    | u1_struct_0(X2) != u1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_38,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | m1_pre_topc(X21,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_39,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_40,plain,(
    ! [X11,X12] :
      ( ( v1_pre_topc(k1_pre_topc(X11,X12))
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))) )
      & ( m1_pre_topc(k1_pre_topc(X11,X12),X11)
        | ~ l1_pre_topc(X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_41,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_26])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25]),c_0_26])])).

cnf(c_0_44,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    | u1_struct_0(X1) != u1_struct_0(esk4_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_37]),c_0_26])])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_48,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_49,plain,(
    ! [X17,X18] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))
      | m1_pre_topc(X18,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_50,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_39])).

cnf(c_0_51,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk4_0,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_54,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | u1_struct_0(esk4_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_26])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_47])).

cnf(c_0_58,plain,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_pre_topc(X2,X3)),u1_pre_topc(k1_pre_topc(X2,X3)))
    | u1_struct_0(X1) != u1_struct_0(k1_pre_topc(X2,X3))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk4_0,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_53])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

fof(c_0_62,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(X10)
      | ~ v1_pre_topc(X10)
      | X10 = g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_63,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_64,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(X1)))) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_42]),c_0_53])])])).

cnf(c_0_66,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_53]),c_0_60])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_61])).

cnf(c_0_68,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_53]),c_0_42])])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_71,plain,
    ( r1_tarski(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_64])).

cnf(c_0_72,plain,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(esk2_0)))) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_53]),c_0_66]),c_0_67])])).

cnf(c_0_74,negated_conjecture,
    ( g1_pre_topc(X1,u1_pre_topc(k1_pre_topc(esk4_0,X1))) = k1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(k1_pre_topc(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_59]),c_0_69])).

cnf(c_0_75,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_70]),c_0_26])])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_70]),c_0_26])])).

fof(c_0_80,plain,(
    ! [X7] : ~ v1_subset_1(k2_subset_1(X7),X7) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

fof(c_0_81,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_82,negated_conjecture,
    ( k1_pre_topc(esk4_0,u1_struct_0(esk2_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ m1_pre_topc(esk4_0,esk4_0)
    | ~ l1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_67])])).

cnf(c_0_83,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( v1_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    | ~ r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_76])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_60]),c_0_79])])).

cnf(c_0_88,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_89,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( k1_pre_topc(esk4_0,u1_struct_0(esk2_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    | ~ l1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_47]),c_0_42])])).

cnf(c_0_91,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_51])).

cnf(c_0_92,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_70]),c_0_26])]),c_0_85])])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( k1_pre_topc(esk4_0,u1_struct_0(esk2_0)) = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_42]),c_0_53]),c_0_67])])).

cnf(c_0_96,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_95]),c_0_67])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:32:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.44  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.18/0.44  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.44  #
% 0.18/0.44  # Preprocessing time       : 0.028 s
% 0.18/0.44  # Presaturation interreduction done
% 0.18/0.44  
% 0.18/0.44  # Proof found!
% 0.18/0.44  # SZS status Theorem
% 0.18/0.44  # SZS output start CNFRefutation
% 0.18/0.44  fof(t14_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 0.18/0.44  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.18/0.44  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.18/0.44  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.44  fof(t5_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(u1_struct_0(X2)=u1_struct_0(X3)=>g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tsep_1)).
% 0.18/0.44  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.18/0.44  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.18/0.44  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.18/0.44  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.18/0.44  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.18/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.44  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.18/0.44  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.18/0.44  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.18/0.44  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.18/0.44  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1)))))), inference(assume_negation,[status(cth)],[t14_tex_2])).
% 0.18/0.44  fof(c_0_17, plain, ![X27, X28, X29]:((~v1_tex_2(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(X29!=u1_struct_0(X28)|v1_subset_1(X29,u1_struct_0(X27))))|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((m1_subset_1(esk1_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))|v1_tex_2(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&((esk1_2(X27,X28)=u1_struct_0(X28)|v1_tex_2(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))&(~v1_subset_1(esk1_2(X27,X28),u1_struct_0(X27))|v1_tex_2(X28,X27)|~m1_pre_topc(X28,X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.18/0.44  fof(c_0_18, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|r1_tarski(u1_struct_0(X23),u1_struct_0(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.18/0.44  fof(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(m1_pre_topc(esk4_0,esk2_0)&((g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))&v1_tex_2(esk3_0,esk2_0))&~v1_tex_2(esk4_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.18/0.44  fof(c_0_20, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|l1_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.44  cnf(c_0_21, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.44  cnf(c_0_22, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.44  fof(c_0_23, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.44  cnf(c_0_24, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.44  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  fof(c_0_27, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|(~m1_pre_topc(X26,X24)|(u1_struct_0(X25)!=u1_struct_0(X26)|g1_pre_topc(u1_struct_0(X25),u1_pre_topc(X25))=g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_tsep_1])])])).
% 0.18/0.44  fof(c_0_28, plain, ![X19, X20]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|~m1_pre_topc(X20,X19)|~l1_pre_topc(X19))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)),X19)|~m1_pre_topc(X20,X19)|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.18/0.44  fof(c_0_29, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|u1_struct_0(k1_pre_topc(X15,X16))=X16)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.18/0.44  cnf(c_0_30, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.44  cnf(c_0_31, negated_conjecture, (~v1_tex_2(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  cnf(c_0_32, plain, (v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.44  fof(c_0_33, plain, ![X31, X32]:((~v1_subset_1(X32,X31)|X32!=X31|~m1_subset_1(X32,k1_zfmisc_1(X31)))&(X32=X31|v1_subset_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.18/0.44  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.44  cnf(c_0_35, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.18/0.44  cnf(c_0_36, plain, (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)|u1_struct_0(X2)!=u1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.44  cnf(c_0_37, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  fof(c_0_38, plain, ![X21]:(~l1_pre_topc(X21)|m1_pre_topc(X21,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.18/0.44  cnf(c_0_39, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.44  fof(c_0_40, plain, ![X11, X12]:((v1_pre_topc(k1_pre_topc(X11,X12))|(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))))&(m1_pre_topc(k1_pre_topc(X11,X12),X11)|(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.18/0.44  cnf(c_0_41, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.44  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_25]), c_0_26])])).
% 0.18/0.44  cnf(c_0_43, negated_conjecture, (~v1_subset_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25]), c_0_26])])).
% 0.18/0.44  cnf(c_0_44, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.44  cnf(c_0_45, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.18/0.44  cnf(c_0_46, negated_conjecture, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))|u1_struct_0(X1)!=u1_struct_0(esk4_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_25]), c_0_37]), c_0_26])])).
% 0.18/0.44  cnf(c_0_47, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.44  fof(c_0_48, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.44  fof(c_0_49, plain, ![X17, X18]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,g1_pre_topc(u1_struct_0(X17),u1_pre_topc(X17)))|m1_pre_topc(X18,X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.18/0.44  cnf(c_0_50, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_30, c_0_39])).
% 0.18/0.44  cnf(c_0_51, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.44  cnf(c_0_52, negated_conjecture, (u1_struct_0(k1_pre_topc(esk4_0,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.44  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.18/0.44  cnf(c_0_54, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|u1_struct_0(esk4_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_26])])).
% 0.18/0.44  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.44  cnf(c_0_56, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.44  cnf(c_0_57, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_50, c_0_47])).
% 0.18/0.44  cnf(c_0_58, plain, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(k1_pre_topc(X2,X3)),u1_pre_topc(k1_pre_topc(X2,X3)))|u1_struct_0(X1)!=u1_struct_0(k1_pre_topc(X2,X3))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_36, c_0_51])).
% 0.18/0.44  cnf(c_0_59, negated_conjecture, (u1_struct_0(k1_pre_topc(esk4_0,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.44  cnf(c_0_60, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_53])])).
% 0.18/0.44  cnf(c_0_61, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 0.18/0.44  fof(c_0_62, plain, ![X10]:(~l1_pre_topc(X10)|(~v1_pre_topc(X10)|X10=g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.18/0.44  cnf(c_0_63, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.44  cnf(c_0_64, plain, (m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_51]), c_0_57])).
% 0.18/0.44  cnf(c_0_65, negated_conjecture, (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(X1))))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_42]), c_0_53])])])).
% 0.18/0.44  cnf(c_0_66, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk4_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_53]), c_0_60])).
% 0.18/0.44  cnf(c_0_67, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_61])).
% 0.18/0.44  cnf(c_0_68, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.44  cnf(c_0_69, negated_conjecture, (v1_pre_topc(k1_pre_topc(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_53]), c_0_42])])).
% 0.18/0.44  cnf(c_0_70, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  cnf(c_0_71, plain, (r1_tarski(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))), inference(spm,[status(thm)],[c_0_24, c_0_64])).
% 0.18/0.44  cnf(c_0_72, plain, (u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))), inference(spm,[status(thm)],[c_0_41, c_0_57])).
% 0.18/0.44  cnf(c_0_73, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(esk2_0))))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~m1_pre_topc(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_53]), c_0_66]), c_0_67])])).
% 0.18/0.44  cnf(c_0_74, negated_conjecture, (g1_pre_topc(X1,u1_pre_topc(k1_pre_topc(esk4_0,X1)))=k1_pre_topc(esk4_0,X1)|~l1_pre_topc(k1_pre_topc(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_59]), c_0_69])).
% 0.18/0.44  cnf(c_0_75, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.44  cnf(c_0_76, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_70]), c_0_26])])).
% 0.18/0.44  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.44  cnf(c_0_78, plain, (r1_tarski(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.18/0.44  cnf(c_0_79, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_70]), c_0_26])])).
% 0.18/0.44  fof(c_0_80, plain, ![X7]:~v1_subset_1(k2_subset_1(X7),X7), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.18/0.44  fof(c_0_81, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.18/0.44  cnf(c_0_82, negated_conjecture, (k1_pre_topc(esk4_0,u1_struct_0(esk2_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~m1_pre_topc(esk4_0,esk4_0)|~l1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_67])])).
% 0.18/0.44  cnf(c_0_83, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_75])).
% 0.18/0.44  cnf(c_0_84, negated_conjecture, (v1_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.44  cnf(c_0_85, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_76])).
% 0.18/0.44  cnf(c_0_86, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)|~r1_tarski(u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_77, c_0_76])).
% 0.18/0.44  cnf(c_0_87, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_60]), c_0_79])])).
% 0.18/0.44  cnf(c_0_88, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.18/0.44  cnf(c_0_89, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.18/0.44  cnf(c_0_90, negated_conjecture, (k1_pre_topc(esk4_0,u1_struct_0(esk2_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))|~l1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_47]), c_0_42])])).
% 0.18/0.44  cnf(c_0_91, plain, (l1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_30, c_0_51])).
% 0.18/0.44  cnf(c_0_92, negated_conjecture, (v1_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_70]), c_0_26])]), c_0_85])])).
% 0.18/0.44  cnf(c_0_93, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.18/0.44  cnf(c_0_94, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 0.18/0.44  cnf(c_0_95, negated_conjecture, (k1_pre_topc(esk4_0,u1_struct_0(esk2_0))=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_42]), c_0_53]), c_0_67])])).
% 0.18/0.44  cnf(c_0_96, negated_conjecture, (~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.18/0.44  cnf(c_0_97, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_95]), c_0_67])])).
% 0.18/0.44  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_67])]), ['proof']).
% 0.18/0.44  # SZS output end CNFRefutation
% 0.18/0.44  # Proof object total steps             : 99
% 0.18/0.44  # Proof object clause steps            : 66
% 0.18/0.44  # Proof object formula steps           : 33
% 0.18/0.44  # Proof object conjectures             : 37
% 0.18/0.44  # Proof object clause conjectures      : 34
% 0.18/0.44  # Proof object formula conjectures     : 3
% 0.18/0.44  # Proof object initial clauses used    : 25
% 0.18/0.44  # Proof object initial formulas used   : 16
% 0.18/0.44  # Proof object generating inferences   : 34
% 0.18/0.44  # Proof object simplifying inferences  : 58
% 0.18/0.44  # Training examples: 0 positive, 0 negative
% 0.18/0.44  # Parsed axioms                        : 16
% 0.18/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.44  # Initial clauses                      : 30
% 0.18/0.44  # Removed in clause preprocessing      : 1
% 0.18/0.44  # Initial clauses in saturation        : 29
% 0.18/0.44  # Processed clauses                    : 850
% 0.18/0.44  # ...of these trivial                  : 63
% 0.18/0.44  # ...subsumed                          : 390
% 0.18/0.44  # ...remaining for further processing  : 397
% 0.18/0.44  # Other redundant clauses eliminated   : 42
% 0.18/0.44  # Clauses deleted for lack of memory   : 0
% 0.18/0.44  # Backward-subsumed                    : 8
% 0.18/0.44  # Backward-rewritten                   : 104
% 0.18/0.44  # Generated clauses                    : 3149
% 0.18/0.44  # ...of the previous two non-trivial   : 2681
% 0.18/0.44  # Contextual simplify-reflections      : 14
% 0.18/0.44  # Paramodulations                      : 3102
% 0.18/0.44  # Factorizations                       : 0
% 0.18/0.44  # Equation resolutions                 : 47
% 0.18/0.44  # Propositional unsat checks           : 0
% 0.18/0.44  #    Propositional check models        : 0
% 0.18/0.44  #    Propositional check unsatisfiable : 0
% 0.18/0.44  #    Propositional clauses             : 0
% 0.18/0.44  #    Propositional clauses after purity: 0
% 0.18/0.44  #    Propositional unsat core size     : 0
% 0.18/0.44  #    Propositional preprocessing time  : 0.000
% 0.18/0.44  #    Propositional encoding time       : 0.000
% 0.18/0.44  #    Propositional solver time         : 0.000
% 0.18/0.44  #    Success case prop preproc time    : 0.000
% 0.18/0.44  #    Success case prop encoding time   : 0.000
% 0.18/0.44  #    Success case prop solver time     : 0.000
% 0.18/0.44  # Current number of processed clauses  : 254
% 0.18/0.44  #    Positive orientable unit clauses  : 27
% 0.18/0.44  #    Positive unorientable unit clauses: 0
% 0.18/0.44  #    Negative unit clauses             : 3
% 0.18/0.44  #    Non-unit-clauses                  : 224
% 0.18/0.44  # Current number of unprocessed clauses: 1762
% 0.18/0.44  # ...number of literals in the above   : 5857
% 0.18/0.44  # Current number of archived formulas  : 0
% 0.18/0.44  # Current number of archived clauses   : 140
% 0.18/0.44  # Clause-clause subsumption calls (NU) : 7404
% 0.18/0.44  # Rec. Clause-clause subsumption calls : 5609
% 0.18/0.44  # Non-unit clause-clause subsumptions  : 259
% 0.18/0.44  # Unit Clause-clause subsumption calls : 330
% 0.18/0.44  # Rewrite failures with RHS unbound    : 0
% 0.18/0.44  # BW rewrite match attempts            : 126
% 0.18/0.44  # BW rewrite match successes           : 11
% 0.18/0.44  # Condensation attempts                : 0
% 0.18/0.44  # Condensation successes               : 0
% 0.18/0.44  # Termbank termtop insertions          : 109368
% 0.18/0.44  
% 0.18/0.44  # -------------------------------------------------
% 0.18/0.44  # User time                : 0.108 s
% 0.18/0.44  # System time              : 0.008 s
% 0.18/0.44  # Total time               : 0.116 s
% 0.18/0.44  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
