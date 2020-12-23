%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:24 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   97 (2753 expanded)
%              Number of clauses        :   70 (1082 expanded)
%              Number of leaves         :   13 ( 684 expanded)
%              Depth                    :   28
%              Number of atoms          :  323 (10081 expanded)
%              Number of equality atoms :   17 (1121 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

fof(d3_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,u1_pre_topc(X1))
             => r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t33_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v3_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v3_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v3_tdlat_3(X1) )
             => v3_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_tex_2])).

fof(c_0_14,plain,(
    ! [X29,X30] :
      ( ( ~ v3_tdlat_3(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r2_hidden(X30,u1_pre_topc(X29))
        | r2_hidden(k6_subset_1(u1_struct_0(X29),X30),u1_pre_topc(X29))
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk1_1(X29),k1_zfmisc_1(u1_struct_0(X29)))
        | v3_tdlat_3(X29)
        | ~ l1_pre_topc(X29) )
      & ( r2_hidden(esk1_1(X29),u1_pre_topc(X29))
        | v3_tdlat_3(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ r2_hidden(k6_subset_1(u1_struct_0(X29),esk1_1(X29)),u1_pre_topc(X29))
        | v3_tdlat_3(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).

fof(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & l1_pre_topc(esk3_0)
    & g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    & v3_tdlat_3(esk2_0)
    & ~ v3_tdlat_3(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( ~ v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
      | m1_pre_topc(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_21,plain,(
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

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | l1_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_25,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_32,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | r1_tarski(u1_struct_0(X28),u1_struct_0(X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_26]),c_0_27])])).

fof(c_0_40,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_pre_topc(X26,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,esk3_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_39]),c_0_18])])).

cnf(c_0_44,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | ~ m1_pre_topc(X24,X22)
      | ~ v3_pre_topc(X23,X22)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | X25 != X23
      | v3_pre_topc(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,esk3_0)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_41]),c_0_29])).

cnf(c_0_47,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_27])])).

cnf(c_0_49,plain,
    ( v3_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_18])])).

fof(c_0_51,plain,(
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

cnf(c_0_52,plain,
    ( r2_hidden(esk1_1(X1),u1_pre_topc(X1))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_53,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | m1_subset_1(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_54,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(X14)
      | m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_18])])).

cnf(c_0_56,plain,
    ( v3_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ v3_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_36]),c_0_48])])).

cnf(c_0_58,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_18]),c_0_19])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(esk1_1(esk3_0),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_24]),c_0_18]),c_0_59])])).

cnf(c_0_65,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_44]),c_0_18])])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_18])])).

cnf(c_0_68,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_27])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_27])])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_67]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_69])).

cnf(c_0_72,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_73,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_75,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_36]),c_0_48])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk3_0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_71]),c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk2_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_66]),c_0_73]),c_0_27])]),c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_66]),c_0_27])])).

cnf(c_0_79,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_36]),c_0_48])])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk3_0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_24]),c_0_79])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_44]),c_0_18])])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_66]),c_0_27])])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)
    | ~ m1_pre_topc(esk3_0,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_36])).

cnf(c_0_87,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_44]),c_0_18])])).

cnf(c_0_88,plain,
    ( v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_65])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(esk3_0))
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_84]),c_0_18])])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_77]),c_0_27]),c_0_81])])).

cnf(c_0_92,plain,
    ( v3_tdlat_3(X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(esk3_0))
    | ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_18])]),c_0_19])).

cnf(c_0_95,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_36])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_44]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:15:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.58  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.39/0.58  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.39/0.58  #
% 0.39/0.58  # Preprocessing time       : 0.028 s
% 0.39/0.58  # Presaturation interreduction done
% 0.39/0.58  
% 0.39/0.58  # Proof found!
% 0.39/0.58  # SZS status Theorem
% 0.39/0.58  # SZS output start CNFRefutation
% 0.39/0.58  fof(t19_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tex_2)).
% 0.39/0.58  fof(d3_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))=>r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tdlat_3)).
% 0.39/0.58  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.39/0.58  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.39/0.58  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.39/0.58  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.39/0.58  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.39/0.58  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.39/0.58  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.39/0.58  fof(t33_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 0.39/0.58  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.39/0.58  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.39/0.58  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.39/0.58  fof(c_0_13, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t19_tex_2])).
% 0.39/0.58  fof(c_0_14, plain, ![X29, X30]:((~v3_tdlat_3(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~r2_hidden(X30,u1_pre_topc(X29))|r2_hidden(k6_subset_1(u1_struct_0(X29),X30),u1_pre_topc(X29))))|~l1_pre_topc(X29))&((m1_subset_1(esk1_1(X29),k1_zfmisc_1(u1_struct_0(X29)))|v3_tdlat_3(X29)|~l1_pre_topc(X29))&((r2_hidden(esk1_1(X29),u1_pre_topc(X29))|v3_tdlat_3(X29)|~l1_pre_topc(X29))&(~r2_hidden(k6_subset_1(u1_struct_0(X29),esk1_1(X29)),u1_pre_topc(X29))|v3_tdlat_3(X29)|~l1_pre_topc(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).
% 0.39/0.58  fof(c_0_15, negated_conjecture, (l1_pre_topc(esk2_0)&(l1_pre_topc(esk3_0)&((g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))&v3_tdlat_3(esk2_0))&~v3_tdlat_3(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.39/0.58  fof(c_0_16, plain, ![X15, X16, X17]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.39/0.58  cnf(c_0_17, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.58  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.58  cnf(c_0_19, negated_conjecture, (~v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.58  fof(c_0_20, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|m1_pre_topc(X19,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.39/0.58  fof(c_0_21, plain, ![X20, X21]:((~m1_pre_topc(X20,X21)|m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(~m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|m1_pre_topc(X20,X21)|~l1_pre_topc(X21)|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.39/0.58  fof(c_0_22, plain, ![X12, X13]:(~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|l1_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.39/0.58  cnf(c_0_23, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.39/0.58  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.39/0.58  cnf(c_0_25, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.39/0.58  cnf(c_0_26, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.58  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.58  cnf(c_0_28, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.39/0.58  cnf(c_0_29, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.58  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.39/0.58  cnf(c_0_31, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.39/0.58  cnf(c_0_32, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.39/0.58  fof(c_0_33, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.39/0.58  fof(c_0_34, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|r1_tarski(u1_struct_0(X28),u1_struct_0(X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.39/0.58  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_30]), c_0_29])).
% 0.39/0.58  cnf(c_0_36, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_18])])).
% 0.39/0.58  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.58  cnf(c_0_38, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.58  cnf(c_0_39, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_26]), c_0_27])])).
% 0.39/0.58  fof(c_0_40, plain, ![X26]:(~l1_pre_topc(X26)|m1_pre_topc(X26,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.39/0.58  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,esk3_0)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.39/0.58  cnf(c_0_42, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.39/0.58  cnf(c_0_43, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_39]), c_0_18])])).
% 0.39/0.58  cnf(c_0_44, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.39/0.58  fof(c_0_45, plain, ![X22, X23, X24, X25]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(~m1_pre_topc(X24,X22)|(~v3_pre_topc(X23,X22)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(X25!=X23|v3_pre_topc(X25,X24))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).
% 0.39/0.58  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,esk3_0)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_41]), c_0_29])).
% 0.39/0.58  cnf(c_0_47, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_38]), c_0_29])).
% 0.39/0.58  cnf(c_0_48, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_27])])).
% 0.39/0.58  cnf(c_0_49, plain, (v3_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.39/0.58  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_44]), c_0_18])])).
% 0.39/0.58  fof(c_0_51, plain, ![X10, X11]:((~v3_pre_topc(X11,X10)|r2_hidden(X11,u1_pre_topc(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(~r2_hidden(X11,u1_pre_topc(X10))|v3_pre_topc(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.39/0.58  cnf(c_0_52, plain, (r2_hidden(esk1_1(X1),u1_pre_topc(X1))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.58  fof(c_0_53, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|m1_subset_1(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.39/0.58  fof(c_0_54, plain, ![X14]:(~l1_pre_topc(X14)|m1_subset_1(u1_pre_topc(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.39/0.58  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)|~m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_18])])).
% 0.39/0.58  cnf(c_0_56, plain, (v3_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~v3_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_49]), c_0_23])).
% 0.39/0.58  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_36]), c_0_48])])).
% 0.39/0.58  cnf(c_0_58, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.39/0.58  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_18]), c_0_19])).
% 0.39/0.58  cnf(c_0_60, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.39/0.58  cnf(c_0_61, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.39/0.58  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_36])).
% 0.39/0.58  cnf(c_0_63, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,X2)|~v3_pre_topc(esk1_1(esk3_0),X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_29])).
% 0.39/0.58  cnf(c_0_64, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_24]), c_0_18]), c_0_59])])).
% 0.39/0.58  cnf(c_0_65, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.39/0.58  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_44]), c_0_18])])).
% 0.39/0.58  cnf(c_0_67, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_18])])).
% 0.39/0.58  cnf(c_0_68, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_36]), c_0_27])])).
% 0.39/0.58  cnf(c_0_69, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_27])])).
% 0.39/0.58  cnf(c_0_70, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_67]), c_0_68])).
% 0.39/0.58  cnf(c_0_71, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(esk3_0,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_69])).
% 0.39/0.58  cnf(c_0_72, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.58  cnf(c_0_73, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.39/0.58  cnf(c_0_74, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.39/0.58  cnf(c_0_75, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),esk2_0)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_36]), c_0_48])])).
% 0.39/0.58  cnf(c_0_76, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(esk3_0,X3)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_71]), c_0_29])).
% 0.39/0.58  cnf(c_0_77, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk3_0),X1),u1_pre_topc(esk2_0))|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_66]), c_0_73]), c_0_27])]), c_0_69])).
% 0.39/0.58  cnf(c_0_78, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk2_0))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_66]), c_0_27])])).
% 0.39/0.58  cnf(c_0_79, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_36]), c_0_48])])).
% 0.39/0.58  cnf(c_0_80, negated_conjecture, (m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(esk3_0,X3)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.39/0.58  cnf(c_0_81, negated_conjecture, (r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_24]), c_0_79])])).
% 0.39/0.58  cnf(c_0_82, negated_conjecture, (m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.39/0.58  cnf(c_0_83, negated_conjecture, (m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_44]), c_0_18])])).
% 0.39/0.58  cnf(c_0_84, negated_conjecture, (m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_66]), c_0_27])])).
% 0.39/0.58  cnf(c_0_85, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)|~m1_pre_topc(esk3_0,esk2_0)|~m1_pre_topc(esk3_0,X1)|~v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_56, c_0_84])).
% 0.39/0.58  cnf(c_0_86, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)|~m1_pre_topc(esk3_0,esk3_0)|~m1_pre_topc(esk3_0,X1)|~v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_85, c_0_36])).
% 0.39/0.58  cnf(c_0_87, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)|~m1_pre_topc(esk3_0,X1)|~v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_44]), c_0_18])])).
% 0.39/0.58  cnf(c_0_88, plain, (v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_58, c_0_65])).
% 0.39/0.58  cnf(c_0_89, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.39/0.58  cnf(c_0_90, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(esk3_0))|~m1_pre_topc(esk3_0,esk2_0)|~v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_84]), c_0_18])])).
% 0.39/0.58  cnf(c_0_91, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),esk3_0)|~m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_77]), c_0_27]), c_0_81])])).
% 0.39/0.58  cnf(c_0_92, plain, (v3_tdlat_3(X1)|~r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.39/0.58  cnf(c_0_93, negated_conjecture, (r2_hidden(k6_subset_1(u1_struct_0(esk3_0),esk1_1(esk3_0)),u1_pre_topc(esk3_0))|~m1_pre_topc(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.39/0.58  cnf(c_0_94, negated_conjecture, (~m1_pre_topc(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_18])]), c_0_19])).
% 0.39/0.58  cnf(c_0_95, negated_conjecture, (~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_94, c_0_36])).
% 0.39/0.58  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_44]), c_0_18])]), ['proof']).
% 0.39/0.58  # SZS output end CNFRefutation
% 0.39/0.58  # Proof object total steps             : 97
% 0.39/0.58  # Proof object clause steps            : 70
% 0.39/0.58  # Proof object formula steps           : 27
% 0.39/0.58  # Proof object conjectures             : 51
% 0.39/0.58  # Proof object clause conjectures      : 48
% 0.39/0.58  # Proof object formula conjectures     : 3
% 0.39/0.58  # Proof object initial clauses used    : 21
% 0.39/0.58  # Proof object initial formulas used   : 13
% 0.39/0.58  # Proof object generating inferences   : 47
% 0.39/0.58  # Proof object simplifying inferences  : 66
% 0.39/0.58  # Training examples: 0 positive, 0 negative
% 0.39/0.58  # Parsed axioms                        : 13
% 0.39/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.58  # Initial clauses                      : 24
% 0.39/0.58  # Removed in clause preprocessing      : 0
% 0.39/0.58  # Initial clauses in saturation        : 24
% 0.39/0.58  # Processed clauses                    : 1328
% 0.39/0.58  # ...of these trivial                  : 5
% 0.39/0.58  # ...subsumed                          : 805
% 0.39/0.58  # ...remaining for further processing  : 518
% 0.39/0.58  # Other redundant clauses eliminated   : 3
% 0.39/0.58  # Clauses deleted for lack of memory   : 0
% 0.39/0.58  # Backward-subsumed                    : 111
% 0.39/0.58  # Backward-rewritten                   : 9
% 0.39/0.58  # Generated clauses                    : 4231
% 0.39/0.58  # ...of the previous two non-trivial   : 3685
% 0.39/0.58  # Contextual simplify-reflections      : 81
% 0.39/0.58  # Paramodulations                      : 4228
% 0.39/0.58  # Factorizations                       : 0
% 0.39/0.58  # Equation resolutions                 : 3
% 0.39/0.58  # Propositional unsat checks           : 0
% 0.39/0.58  #    Propositional check models        : 0
% 0.39/0.58  #    Propositional check unsatisfiable : 0
% 0.39/0.58  #    Propositional clauses             : 0
% 0.39/0.58  #    Propositional clauses after purity: 0
% 0.39/0.58  #    Propositional unsat core size     : 0
% 0.39/0.58  #    Propositional preprocessing time  : 0.000
% 0.39/0.58  #    Propositional encoding time       : 0.000
% 0.39/0.58  #    Propositional solver time         : 0.000
% 0.39/0.58  #    Success case prop preproc time    : 0.000
% 0.39/0.58  #    Success case prop encoding time   : 0.000
% 0.39/0.58  #    Success case prop solver time     : 0.000
% 0.39/0.58  # Current number of processed clauses  : 373
% 0.39/0.58  #    Positive orientable unit clauses  : 13
% 0.39/0.58  #    Positive unorientable unit clauses: 0
% 0.39/0.58  #    Negative unit clauses             : 3
% 0.39/0.58  #    Non-unit-clauses                  : 357
% 0.39/0.58  # Current number of unprocessed clauses: 2263
% 0.39/0.58  # ...number of literals in the above   : 15154
% 0.39/0.58  # Current number of archived formulas  : 0
% 0.39/0.58  # Current number of archived clauses   : 142
% 0.39/0.58  # Clause-clause subsumption calls (NU) : 62994
% 0.39/0.58  # Rec. Clause-clause subsumption calls : 12015
% 0.39/0.58  # Non-unit clause-clause subsumptions  : 991
% 0.39/0.58  # Unit Clause-clause subsumption calls : 565
% 0.39/0.58  # Rewrite failures with RHS unbound    : 0
% 0.39/0.58  # BW rewrite match attempts            : 3
% 0.39/0.58  # BW rewrite match successes           : 3
% 0.39/0.58  # Condensation attempts                : 0
% 0.39/0.58  # Condensation successes               : 0
% 0.39/0.58  # Termbank termtop insertions          : 212103
% 0.39/0.59  
% 0.39/0.59  # -------------------------------------------------
% 0.39/0.59  # User time                : 0.229 s
% 0.39/0.59  # System time              : 0.010 s
% 0.39/0.59  # Total time               : 0.240 s
% 0.39/0.59  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
