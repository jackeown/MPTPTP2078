%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:25 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   85 (1833 expanded)
%              Number of clauses        :   58 ( 726 expanded)
%              Number of leaves         :   13 ( 454 expanded)
%              Depth                    :   20
%              Number of atoms          :  270 (6442 expanded)
%              Number of equality atoms :   25 ( 851 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t19_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v3_tdlat_3(X1) )
           => v3_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t78_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> r1_tarski(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(t35_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v1_tops_2(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                   => ( X4 = X2
                     => v1_tops_2(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(fc5_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => v1_tops_2(u1_pre_topc(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_compts_1)).

fof(d3_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,u1_pre_topc(X1))
             => r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(c_0_13,plain,(
    ! [X15,X16] :
      ( ( ~ m1_pre_topc(X15,X16)
        | m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | m1_pre_topc(X15,X16)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v3_tdlat_3(X1) )
             => v3_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_tex_2])).

cnf(c_0_16,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & l1_pre_topc(esk3_0)
    & g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    & v3_tdlat_3(esk2_0)
    & ~ v3_tdlat_3(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_20,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | r1_tarski(u1_struct_0(X26),u1_struct_0(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))
      | m1_pre_topc(X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_22,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | m1_pre_topc(X24,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_31,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_33,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24])])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_24])])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_29])])).

fof(c_0_39,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(X12)
      | m1_subset_1(u1_pre_topc(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_41,plain,(
    ! [X21,X22] :
      ( ( ~ v1_tops_2(X22,X21)
        | r1_tarski(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_tarski(X22,u1_pre_topc(X21))
        | v1_tops_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).

cnf(c_0_42,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_29])])).

fof(c_0_44,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))
      | ~ m1_pre_topc(X19,X17)
      | ~ v1_tops_2(X18,X17)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))
      | X20 != X18
      | v1_tops_2(X20,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,u1_pre_topc(X2))
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_24])])).

cnf(c_0_47,plain,
    ( v1_tops_2(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( v1_tops_2(X1,X2)
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk3_0))
    | ~ v1_tops_2(u1_pre_topc(esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,u1_pre_topc(esk2_0))
    | ~ v1_tops_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_24])])).

cnf(c_0_52,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v1_tops_2(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | ~ r1_tarski(X1,u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_24])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk2_0),esk3_0)
    | ~ r1_tarski(u1_pre_topc(esk3_0),u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk3_0),u1_pre_topc(esk2_0))
    | ~ v1_tops_2(u1_pre_topc(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_42]),c_0_29])])).

cnf(c_0_57,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk2_0),esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk2_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( v1_tops_2(X1,esk2_0)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk2_0),esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk2_0),esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_43]),c_0_58]),c_0_24]),c_0_46])])).

cnf(c_0_62,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk2_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_42]),c_0_29])])).

fof(c_0_63,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | m1_subset_1(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_64,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),esk2_0)
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk2_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_42]),c_0_35]),c_0_29])])).

fof(c_0_66,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | v1_tops_2(u1_pre_topc(X23),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_compts_1])])).

fof(c_0_67,plain,(
    ! [X27,X28] :
      ( ( ~ v3_tdlat_3(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ r2_hidden(X28,u1_pre_topc(X27))
        | r2_hidden(k6_subset_1(u1_struct_0(X27),X28),u1_pre_topc(X27))
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk1_1(X27),k1_zfmisc_1(u1_struct_0(X27)))
        | v3_tdlat_3(X27)
        | ~ l1_pre_topc(X27) )
      & ( r2_hidden(esk1_1(X27),u1_pre_topc(X27))
        | v3_tdlat_3(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r2_hidden(k6_subset_1(u1_struct_0(X27),esk1_1(X27)),u1_pre_topc(X27))
        | v3_tdlat_3(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( v1_tops_2(u1_pre_topc(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_42])).

cnf(c_0_73,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_29])])).

cnf(c_0_74,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(csr,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_76,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_38])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk2_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_43]),c_0_75]),c_0_24])])).

cnf(c_0_78,negated_conjecture,
    ( u1_pre_topc(esk2_0) = u1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_33]),c_0_29])])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_1(X1),u1_pre_topc(X1))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( ~ v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_81,plain,
    ( v3_tdlat_3(X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk3_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_29]),c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_29]),c_0_83])]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.030 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t19_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tex_2)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.13/0.38  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.13/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.13/0.38  fof(t78_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>r1_tarski(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 0.13/0.38  fof(t35_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v1_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v1_tops_2(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(fc5_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>v1_tops_2(u1_pre_topc(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_compts_1)).
% 0.13/0.38  fof(d3_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))=>r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tdlat_3)).
% 0.13/0.38  fof(c_0_13, plain, ![X15, X16]:((~m1_pre_topc(X15,X16)|m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&(~m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|m1_pre_topc(X15,X16)|~l1_pre_topc(X16)|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_15, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t19_tex_2])).
% 0.13/0.38  cnf(c_0_16, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_17, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)&(l1_pre_topc(esk3_0)&((g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))&v3_tdlat_3(esk2_0))&~v3_tdlat_3(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_20, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|r1_tarski(u1_struct_0(X26),u1_struct_0(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X13, X14]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13)))|m1_pre_topc(X14,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.13/0.38  cnf(c_0_22, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_25, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_26, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_27, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_30, plain, ![X24]:(~l1_pre_topc(X24)|m1_pre_topc(X24,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.38  cnf(c_0_31, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.13/0.38  cnf(c_0_33, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_34, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_26]), c_0_17])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_23]), c_0_24])])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)|~m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_22]), c_0_29])])).
% 0.13/0.38  fof(c_0_39, plain, ![X12]:(~l1_pre_topc(X12)|m1_subset_1(u1_pre_topc(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  fof(c_0_41, plain, ![X21, X22]:((~v1_tops_2(X22,X21)|r1_tarski(X22,u1_pre_topc(X21))|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|~l1_pre_topc(X21))&(~r1_tarski(X22,u1_pre_topc(X21))|v1_tops_2(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_tops_2])])])])).
% 0.13/0.38  cnf(c_0_42, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_33]), c_0_29])])).
% 0.13/0.38  fof(c_0_44, plain, ![X17, X18, X19, X20]:(~l1_pre_topc(X17)|(~m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17))))|(~m1_pre_topc(X19,X17)|(~v1_tops_2(X18,X17)|(~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X19))))|(X20!=X18|v1_tops_2(X20,X19))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).
% 0.13/0.38  cnf(c_0_45, plain, (r1_tarski(X1,u1_pre_topc(X2))|~v1_tops_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_24])])).
% 0.13/0.38  cnf(c_0_47, plain, (v1_tops_2(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_pre_topc(X3,X1)|~v1_tops_2(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_48, plain, (v1_tops_2(X1,X2)|~r1_tarski(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk3_0))|~v1_tops_2(u1_pre_topc(esk2_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_29])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,u1_pre_topc(esk2_0))|~v1_tops_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_24])])).
% 0.13/0.38  cnf(c_0_52, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_47])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (v1_tops_2(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))|~r1_tarski(X1,u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_43]), c_0_24])])).
% 0.13/0.38  cnf(c_0_54, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)|~v1_tops_2(u1_pre_topc(esk2_0),esk3_0)|~r1_tarski(u1_pre_topc(esk3_0),u1_pre_topc(esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_50])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (r1_tarski(u1_pre_topc(esk3_0),u1_pre_topc(esk2_0))|~v1_tops_2(u1_pre_topc(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_42]), c_0_29])])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (v1_tops_2(u1_pre_topc(esk2_0),esk3_0)|~v1_tops_2(u1_pre_topc(esk2_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_52, c_0_46])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (v1_tops_2(u1_pre_topc(esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_54])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (v1_tops_2(X1,esk2_0)|~v1_tops_2(X1,X2)|~m1_pre_topc(esk2_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(spm,[status(thm)],[c_0_52, c_0_43])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)|~v1_tops_2(u1_pre_topc(esk2_0),esk3_0)|~v1_tops_2(u1_pre_topc(esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (v1_tops_2(u1_pre_topc(esk2_0),esk3_0)|~m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_43]), c_0_58]), c_0_24]), c_0_46])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk2_0)|~v1_tops_2(u1_pre_topc(esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_42]), c_0_29])])).
% 0.13/0.38  fof(c_0_63, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|m1_subset_1(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)|~v1_tops_2(u1_pre_topc(esk3_0),esk2_0)|~m1_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk2_0)|~v1_tops_2(u1_pre_topc(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_42]), c_0_35]), c_0_29])])).
% 0.13/0.38  fof(c_0_66, plain, ![X23]:(~l1_pre_topc(X23)|v1_tops_2(u1_pre_topc(X23),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_compts_1])])).
% 0.13/0.38  fof(c_0_67, plain, ![X27, X28]:((~v3_tdlat_3(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~r2_hidden(X28,u1_pre_topc(X27))|r2_hidden(k6_subset_1(u1_struct_0(X27),X28),u1_pre_topc(X27))))|~l1_pre_topc(X27))&((m1_subset_1(esk1_1(X27),k1_zfmisc_1(u1_struct_0(X27)))|v3_tdlat_3(X27)|~l1_pre_topc(X27))&((r2_hidden(esk1_1(X27),u1_pre_topc(X27))|v3_tdlat_3(X27)|~l1_pre_topc(X27))&(~r2_hidden(k6_subset_1(u1_struct_0(X27),esk1_1(X27)),u1_pre_topc(X27))|v3_tdlat_3(X27)|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).
% 0.13/0.38  cnf(c_0_68, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.38  cnf(c_0_69, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)|~v1_tops_2(u1_pre_topc(esk3_0),esk3_0)|~m1_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.38  cnf(c_0_70, plain, (v1_tops_2(u1_pre_topc(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.38  cnf(c_0_71, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_68, c_0_42])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)|~m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_29])])).
% 0.13/0.38  cnf(c_0_74, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(csr,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_73, c_0_38])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk2_0))|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_43]), c_0_75]), c_0_24])])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (u1_pre_topc(esk2_0)=u1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_33]), c_0_29])])).
% 0.13/0.38  cnf(c_0_79, plain, (r2_hidden(esk1_1(X1),u1_pre_topc(X1))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_80, negated_conjecture, (~v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_81, plain, (v3_tdlat_3(X1)|~r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk3_0))|~r2_hidden(X1,u1_pre_topc(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_78])).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_29]), c_0_80])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_29]), c_0_83])]), c_0_80]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 85
% 0.13/0.38  # Proof object clause steps            : 58
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 38
% 0.13/0.38  # Proof object clause conjectures      : 35
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 21
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 32
% 0.13/0.38  # Proof object simplifying inferences  : 54
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 24
% 0.13/0.39  # Processed clauses                    : 176
% 0.13/0.39  # ...of these trivial                  : 5
% 0.13/0.39  # ...subsumed                          : 45
% 0.13/0.39  # ...remaining for further processing  : 126
% 0.13/0.39  # Other redundant clauses eliminated   : 3
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 4
% 0.13/0.39  # Backward-rewritten                   : 24
% 0.13/0.39  # Generated clauses                    : 216
% 0.13/0.39  # ...of the previous two non-trivial   : 176
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 213
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 3
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 73
% 0.13/0.39  #    Positive orientable unit clauses  : 12
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 60
% 0.13/0.39  # Current number of unprocessed clauses: 43
% 0.13/0.39  # ...number of literals in the above   : 164
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 50
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1020
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 684
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 52
% 0.13/0.39  # Unit Clause-clause subsumption calls : 13
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 3
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 6824
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.041 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
