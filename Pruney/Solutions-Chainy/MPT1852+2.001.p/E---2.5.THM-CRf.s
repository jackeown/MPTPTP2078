%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 (1205 expanded)
%              Number of clauses        :   65 ( 475 expanded)
%              Number of leaves         :   15 ( 300 expanded)
%              Depth                    :   19
%              Number of atoms          :  330 (4333 expanded)
%              Number of equality atoms :   17 ( 530 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v3_tdlat_3(X1) )
           => v3_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(t31_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
             => m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(d3_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,u1_pre_topc(X1))
             => r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(fc5_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => v1_tops_2(u1_pre_topc(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v3_tdlat_3(X1) )
             => v3_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_tex_2])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ( ~ m1_pre_topc(X20,X21)
        | m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | m1_pre_topc(X20,X21)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_17,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | l1_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X35,X36] :
      ( ~ l1_pre_topc(X35)
      | ~ m1_pre_topc(X36,X35)
      | r1_tarski(u1_struct_0(X36),u1_struct_0(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_20,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
      | m1_pre_topc(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & l1_pre_topc(esk4_0)
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    & v3_tdlat_3(esk3_0)
    & ~ v3_tdlat_3(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_22,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_27]),c_0_28])])).

fof(c_0_34,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | m1_pre_topc(X34,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_35,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_32])])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_33]),c_0_32])])).

cnf(c_0_38,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_28])])).

fof(c_0_41,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | m1_subset_1(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_42,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_43,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_tops_2(X23,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X24,X23)
        | v3_pre_topc(X24,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk1_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk1_2(X22,X23),X23)
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) )
      & ( ~ v3_pre_topc(esk1_2(X22,X23),X22)
        | v1_tops_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk4_0)
    | ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_45,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))
      | ~ m1_pre_topc(X31,X29)
      | ~ v1_tops_2(X30,X29)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))
      | X32 != X30
      | v1_tops_2(X32,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).

fof(c_0_46,plain,(
    ! [X26,X27,X28] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))
      | m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).

fof(c_0_47,plain,(
    ! [X10,X11] :
      ( ( ~ v3_pre_topc(X11,X10)
        | r2_hidden(X11,u1_pre_topc(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(X11,u1_pre_topc(X10))
        | v3_pre_topc(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_32])])).

cnf(c_0_52,plain,
    ( v1_tops_2(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( v1_tops_2(X1,esk3_0)
    | r2_hidden(esk1_2(esk3_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_28])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_51]),c_0_28])])).

cnf(c_0_59,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( v1_tops_2(X1,X2)
    | ~ v1_tops_2(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_53])).

cnf(c_0_61,plain,
    ( v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(esk1_2(X2,X1),u1_pre_topc(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk3_0)
    | r2_hidden(esk1_2(esk3_0,u1_pre_topc(esk3_0)),u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(csr,[status(thm)],[c_0_59,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk4_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_28]),c_0_51]),c_0_58])])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ v1_tops_2(u1_pre_topc(esk3_0),esk4_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58]),c_0_32])])).

cnf(c_0_67,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk3_0),esk4_0)
    | ~ m1_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_28])])).

fof(c_0_68,plain,(
    ! [X37,X38] :
      ( ( ~ v3_tdlat_3(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ r2_hidden(X38,u1_pre_topc(X37))
        | r2_hidden(k6_subset_1(u1_struct_0(X37),X38),u1_pre_topc(X37))
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk2_1(X37),k1_zfmisc_1(u1_struct_0(X37)))
        | v3_tdlat_3(X37)
        | ~ l1_pre_topc(X37) )
      & ( r2_hidden(esk2_1(X37),u1_pre_topc(X37))
        | v3_tdlat_3(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ r2_hidden(k6_subset_1(u1_struct_0(X37),esk2_1(X37)),u1_pre_topc(X37))
        | v3_tdlat_3(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).

cnf(c_0_69,negated_conjecture,
    ( v1_tops_2(X1,esk3_0)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

fof(c_0_70,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | v1_tops_2(u1_pre_topc(X33),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_compts_1])])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_58])).

cnf(c_0_74,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ v1_tops_2(X2,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_51]),c_0_28])])).

cnf(c_0_76,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk4_0),esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk4_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_49]),c_0_32])])).

cnf(c_0_77,plain,
    ( v1_tops_2(u1_pre_topc(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_32])]),c_0_73])).

cnf(c_0_79,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(csr,[status(thm)],[c_0_74,c_0_56])).

cnf(c_0_80,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ v1_tops_2(u1_pre_topc(esk4_0),esk3_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_49]),c_0_32])])).

cnf(c_0_82,negated_conjecture,
    ( v1_tops_2(u1_pre_topc(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_40]),c_0_32])])).

cnf(c_0_83,plain,
    ( v3_tdlat_3(X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X1),esk2_1(X1)),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk4_0),X1),u1_pre_topc(esk4_0))
    | ~ m1_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_51]),c_0_80]),c_0_28])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_87,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_88,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_89,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,esk3_0)
    | ~ r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_32])]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_86]),c_0_28]),c_0_51])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_32]),c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_32]),c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_92])])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_36])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_38]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.55  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.043 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(t19_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tex_2)).
% 0.20/0.55  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.20/0.55  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.55  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.20/0.55  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.20/0.55  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.55  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.55  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.55  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 0.20/0.55  fof(t35_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v1_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v1_tops_2(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_2)).
% 0.20/0.55  fof(t31_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))=>m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_2)).
% 0.20/0.55  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.20/0.55  fof(d3_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))=>r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tdlat_3)).
% 0.20/0.55  fof(fc5_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>v1_tops_2(u1_pre_topc(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_compts_1)).
% 0.20/0.55  fof(c_0_15, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t19_tex_2])).
% 0.20/0.55  fof(c_0_16, plain, ![X20, X21]:((~m1_pre_topc(X20,X21)|m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(~m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|m1_pre_topc(X20,X21)|~l1_pre_topc(X21)|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.20/0.55  fof(c_0_17, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|l1_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.55  fof(c_0_18, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.55  fof(c_0_19, plain, ![X35, X36]:(~l1_pre_topc(X35)|(~m1_pre_topc(X36,X35)|r1_tarski(u1_struct_0(X36),u1_struct_0(X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.20/0.55  fof(c_0_20, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|m1_pre_topc(X19,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.20/0.55  fof(c_0_21, negated_conjecture, (l1_pre_topc(esk3_0)&(l1_pre_topc(esk4_0)&((g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))&v3_tdlat_3(esk3_0))&~v3_tdlat_3(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.20/0.55  cnf(c_0_22, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.55  cnf(c_0_23, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.55  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.55  cnf(c_0_25, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.55  cnf(c_0_26, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.55  cnf(c_0_27, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.55  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.55  cnf(c_0_29, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.55  cnf(c_0_30, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.55  cnf(c_0_31, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.20/0.55  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.55  cnf(c_0_33, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_27]), c_0_28])])).
% 0.20/0.55  fof(c_0_34, plain, ![X34]:(~l1_pre_topc(X34)|m1_pre_topc(X34,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.55  cnf(c_0_35, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_25]), c_0_23])).
% 0.20/0.55  cnf(c_0_36, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_32])])).
% 0.20/0.55  cnf(c_0_37, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_33]), c_0_32])])).
% 0.20/0.55  cnf(c_0_38, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.55  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28])])).
% 0.20/0.55  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_28])])).
% 0.20/0.55  fof(c_0_41, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|m1_subset_1(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.55  fof(c_0_42, plain, ![X14]:(~l1_pre_topc(X14)|m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.55  fof(c_0_43, plain, ![X22, X23, X24]:((~v1_tops_2(X23,X22)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(~r2_hidden(X24,X23)|v3_pre_topc(X24,X22)))|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((m1_subset_1(esk1_2(X22,X23),k1_zfmisc_1(u1_struct_0(X22)))|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&((r2_hidden(esk1_2(X22,X23),X23)|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))&(~v3_pre_topc(esk1_2(X22,X23),X22)|v1_tops_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 0.20/0.55  cnf(c_0_44, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk4_0)|~m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.55  fof(c_0_45, plain, ![X29, X30, X31, X32]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X29))))|(~m1_pre_topc(X31,X29)|(~v1_tops_2(X30,X29)|(~m1_subset_1(X32,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X31))))|(X32!=X30|v1_tops_2(X32,X31))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_tops_2])])])).
% 0.20/0.55  fof(c_0_46, plain, ![X26, X27, X28]:(~l1_pre_topc(X26)|(~m1_pre_topc(X27,X26)|(~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))|m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X26))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_tops_2])])])).
% 0.20/0.55  fof(c_0_47, plain, ![X10, X11]:((~v3_pre_topc(X11,X10)|r2_hidden(X11,u1_pre_topc(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(~r2_hidden(X11,u1_pre_topc(X10))|v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.20/0.55  cnf(c_0_48, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.55  cnf(c_0_49, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.55  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X2)|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.55  cnf(c_0_51, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_32])])).
% 0.20/0.55  cnf(c_0_52, plain, (v1_tops_2(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_pre_topc(X3,X1)|~v1_tops_2(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.55  cnf(c_0_53, plain, (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.55  cnf(c_0_54, plain, (v1_tops_2(X2,X1)|~v3_pre_topc(esk1_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.55  cnf(c_0_55, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.55  cnf(c_0_56, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.55  cnf(c_0_57, negated_conjecture, (v1_tops_2(X1,esk3_0)|r2_hidden(esk1_2(esk3_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_28])])).
% 0.20/0.55  cnf(c_0_58, negated_conjecture, (m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_51]), c_0_28])])).
% 0.20/0.55  cnf(c_0_59, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.55  cnf(c_0_60, plain, (v1_tops_2(X1,X2)|~v1_tops_2(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_53])).
% 0.20/0.55  cnf(c_0_61, plain, (v1_tops_2(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r2_hidden(esk1_2(X2,X1),u1_pre_topc(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.55  cnf(c_0_62, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk3_0)|r2_hidden(esk1_2(esk3_0,u1_pre_topc(esk3_0)),u1_pre_topc(esk3_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.55  cnf(c_0_63, plain, (v3_pre_topc(X1,X2)|~v1_tops_2(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r2_hidden(X1,X3)), inference(csr,[status(thm)],[c_0_59, c_0_48])).
% 0.20/0.55  cnf(c_0_64, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk4_0)|~v1_tops_2(u1_pre_topc(esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_60, c_0_58])).
% 0.20/0.55  cnf(c_0_65, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_28]), c_0_51]), c_0_58])])).
% 0.20/0.55  cnf(c_0_66, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~v1_tops_2(u1_pre_topc(esk3_0),esk4_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_58]), c_0_32])])).
% 0.20/0.55  cnf(c_0_67, negated_conjecture, (v1_tops_2(u1_pre_topc(esk3_0),esk4_0)|~m1_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_28])])).
% 0.20/0.55  fof(c_0_68, plain, ![X37, X38]:((~v3_tdlat_3(X37)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|(~r2_hidden(X38,u1_pre_topc(X37))|r2_hidden(k6_subset_1(u1_struct_0(X37),X38),u1_pre_topc(X37))))|~l1_pre_topc(X37))&((m1_subset_1(esk2_1(X37),k1_zfmisc_1(u1_struct_0(X37)))|v3_tdlat_3(X37)|~l1_pre_topc(X37))&((r2_hidden(esk2_1(X37),u1_pre_topc(X37))|v3_tdlat_3(X37)|~l1_pre_topc(X37))&(~r2_hidden(k6_subset_1(u1_struct_0(X37),esk2_1(X37)),u1_pre_topc(X37))|v3_tdlat_3(X37)|~l1_pre_topc(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).
% 0.20/0.55  cnf(c_0_69, negated_conjecture, (v1_tops_2(X1,esk3_0)|~v1_tops_2(X1,X2)|~m1_pre_topc(esk3_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 0.20/0.55  fof(c_0_70, plain, ![X33]:(~l1_pre_topc(X33)|v1_tops_2(u1_pre_topc(X33),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_compts_1])])).
% 0.20/0.55  cnf(c_0_71, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.55  cnf(c_0_72, negated_conjecture, (v3_pre_topc(X1,esk4_0)|~m1_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.55  cnf(c_0_73, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,u1_pre_topc(esk3_0))), inference(spm,[status(thm)],[c_0_48, c_0_58])).
% 0.20/0.55  cnf(c_0_74, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.55  cnf(c_0_75, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~v1_tops_2(X2,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_51]), c_0_28])])).
% 0.20/0.55  cnf(c_0_76, negated_conjecture, (v1_tops_2(u1_pre_topc(esk4_0),esk3_0)|~v1_tops_2(u1_pre_topc(esk4_0),X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_49]), c_0_32])])).
% 0.20/0.55  cnf(c_0_77, plain, (v1_tops_2(u1_pre_topc(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.55  cnf(c_0_78, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk4_0))|~m1_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_32])]), c_0_73])).
% 0.20/0.55  cnf(c_0_79, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(csr,[status(thm)],[c_0_74, c_0_56])).
% 0.20/0.55  cnf(c_0_80, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.55  cnf(c_0_81, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~v1_tops_2(u1_pre_topc(esk4_0),esk3_0)|~r2_hidden(X1,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_49]), c_0_32])])).
% 0.20/0.55  cnf(c_0_82, negated_conjecture, (v1_tops_2(u1_pre_topc(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_40]), c_0_32])])).
% 0.20/0.55  cnf(c_0_83, plain, (v3_tdlat_3(X1)|~r2_hidden(k6_subset_1(u1_struct_0(X1),esk2_1(X1)),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.55  cnf(c_0_84, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk4_0),X1),u1_pre_topc(esk4_0))|~m1_pre_topc(esk4_0,esk3_0)|~r2_hidden(X1,u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_51]), c_0_80]), c_0_28])])).
% 0.20/0.55  cnf(c_0_85, negated_conjecture, (~v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.55  cnf(c_0_86, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~r2_hidden(X1,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.20/0.55  cnf(c_0_87, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.55  cnf(c_0_88, plain, (r2_hidden(esk2_1(X1),u1_pre_topc(X1))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.55  cnf(c_0_89, negated_conjecture, (~m1_pre_topc(esk4_0,esk3_0)|~r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_32])]), c_0_85])).
% 0.20/0.55  cnf(c_0_90, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_86]), c_0_28]), c_0_51])])).
% 0.20/0.55  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_32]), c_0_85])).
% 0.20/0.55  cnf(c_0_92, negated_conjecture, (r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_32]), c_0_85])).
% 0.20/0.55  cnf(c_0_93, negated_conjecture, (~m1_pre_topc(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_92])])).
% 0.20/0.55  cnf(c_0_94, negated_conjecture, (~m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_93, c_0_36])).
% 0.20/0.55  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_38]), c_0_32])]), ['proof']).
% 0.20/0.55  # SZS output end CNFRefutation
% 0.20/0.55  # Proof object total steps             : 96
% 0.20/0.55  # Proof object clause steps            : 65
% 0.20/0.55  # Proof object formula steps           : 31
% 0.20/0.55  # Proof object conjectures             : 40
% 0.20/0.55  # Proof object clause conjectures      : 37
% 0.20/0.55  # Proof object formula conjectures     : 3
% 0.20/0.55  # Proof object initial clauses used    : 25
% 0.20/0.55  # Proof object initial formulas used   : 15
% 0.20/0.55  # Proof object generating inferences   : 35
% 0.20/0.55  # Proof object simplifying inferences  : 64
% 0.20/0.55  # Training examples: 0 positive, 0 negative
% 0.20/0.55  # Parsed axioms                        : 16
% 0.20/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.55  # Initial clauses                      : 30
% 0.20/0.55  # Removed in clause preprocessing      : 0
% 0.20/0.55  # Initial clauses in saturation        : 30
% 0.20/0.55  # Processed clauses                    : 956
% 0.20/0.55  # ...of these trivial                  : 0
% 0.20/0.55  # ...subsumed                          : 566
% 0.20/0.55  # ...remaining for further processing  : 390
% 0.20/0.55  # Other redundant clauses eliminated   : 3
% 0.20/0.55  # Clauses deleted for lack of memory   : 0
% 0.20/0.55  # Backward-subsumed                    : 31
% 0.20/0.55  # Backward-rewritten                   : 12
% 0.20/0.55  # Generated clauses                    : 3132
% 0.20/0.55  # ...of the previous two non-trivial   : 2712
% 0.20/0.55  # Contextual simplify-reflections      : 43
% 0.20/0.55  # Paramodulations                      : 3129
% 0.20/0.55  # Factorizations                       : 0
% 0.20/0.55  # Equation resolutions                 : 3
% 0.20/0.55  # Propositional unsat checks           : 0
% 0.20/0.55  #    Propositional check models        : 0
% 0.20/0.55  #    Propositional check unsatisfiable : 0
% 0.20/0.55  #    Propositional clauses             : 0
% 0.20/0.55  #    Propositional clauses after purity: 0
% 0.20/0.55  #    Propositional unsat core size     : 0
% 0.20/0.55  #    Propositional preprocessing time  : 0.000
% 0.20/0.55  #    Propositional encoding time       : 0.000
% 0.20/0.55  #    Propositional solver time         : 0.000
% 0.20/0.55  #    Success case prop preproc time    : 0.000
% 0.20/0.55  #    Success case prop encoding time   : 0.000
% 0.20/0.55  #    Success case prop solver time     : 0.000
% 0.20/0.55  # Current number of processed clauses  : 316
% 0.20/0.55  #    Positive orientable unit clauses  : 12
% 0.20/0.55  #    Positive unorientable unit clauses: 0
% 0.20/0.55  #    Negative unit clauses             : 3
% 0.20/0.55  #    Non-unit-clauses                  : 301
% 0.20/0.55  # Current number of unprocessed clauses: 1734
% 0.20/0.55  # ...number of literals in the above   : 12009
% 0.20/0.55  # Current number of archived formulas  : 0
% 0.20/0.55  # Current number of archived clauses   : 71
% 0.20/0.55  # Clause-clause subsumption calls (NU) : 49601
% 0.20/0.55  # Rec. Clause-clause subsumption calls : 7500
% 0.20/0.55  # Non-unit clause-clause subsumptions  : 640
% 0.20/0.55  # Unit Clause-clause subsumption calls : 432
% 0.20/0.55  # Rewrite failures with RHS unbound    : 0
% 0.20/0.55  # BW rewrite match attempts            : 4
% 0.20/0.55  # BW rewrite match successes           : 4
% 0.20/0.55  # Condensation attempts                : 0
% 0.20/0.55  # Condensation successes               : 0
% 0.20/0.55  # Termbank termtop insertions          : 188805
% 0.20/0.55  
% 0.20/0.55  # -------------------------------------------------
% 0.20/0.55  # User time                : 0.192 s
% 0.20/0.55  # System time              : 0.007 s
% 0.20/0.55  # Total time               : 0.199 s
% 0.20/0.55  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
