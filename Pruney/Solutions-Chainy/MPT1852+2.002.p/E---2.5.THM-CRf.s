%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:24 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   96 (1512 expanded)
%              Number of clauses        :   67 ( 599 expanded)
%              Number of leaves         :   14 ( 377 expanded)
%              Depth                    :   20
%              Number of atoms          :  315 (5431 expanded)
%              Number of equality atoms :   19 ( 610 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t19_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v3_tdlat_3(X1) )
           => v3_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(d3_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r2_hidden(X2,u1_pre_topc(X1))
             => r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_14,plain,(
    ! [X22,X23] :
      ( ( ~ m1_pre_topc(X22,X23)
        | m1_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))
        | m1_pre_topc(X22,X23)
        | ~ l1_pre_topc(X23)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_15,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v3_tdlat_3(X1) )
             => v3_tdlat_3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_tex_2])).

cnf(c_0_17,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & l1_pre_topc(esk3_0)
    & g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    & v3_tdlat_3(esk2_0)
    & ~ v3_tdlat_3(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
      | m1_pre_topc(X21,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,X28)
      | m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(X28))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_30,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_33,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | m1_pre_topc(X30,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_34,plain,(
    ! [X31,X32] :
      ( ( ~ v3_tdlat_3(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r2_hidden(X32,u1_pre_topc(X31))
        | r2_hidden(k6_subset_1(u1_struct_0(X31),X32),u1_pre_topc(X31))
        | ~ l1_pre_topc(X31) )
      & ( m1_subset_1(esk1_1(X31),k1_zfmisc_1(u1_struct_0(X31)))
        | v3_tdlat_3(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(esk1_1(X31),u1_pre_topc(X31))
        | v3_tdlat_3(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ r2_hidden(k6_subset_1(u1_struct_0(X31),esk1_1(X31)),u1_pre_topc(X31))
        | v3_tdlat_3(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_43,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_25])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_32]),c_0_41])).

cnf(c_0_46,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32])])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_25])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_23]),c_0_32])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_49]),c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk2_0,esk2_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_25])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,esk3_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

fof(c_0_55,plain,(
    ! [X16] :
      ( ~ l1_pre_topc(X16)
      | m1_subset_1(u1_pre_topc(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0)
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_39]),c_0_25])])).

fof(c_0_57,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_58,plain,(
    ! [X24,X25,X26,X27] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_pre_topc(X26,X24)
      | ~ v3_pre_topc(X25,X24)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | X27 != X25
      | v3_pre_topc(X27,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,esk3_0)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_54]),c_0_18])).

cnf(c_0_60,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_39]),c_0_32])])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_63,plain,
    ( v3_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_39]),c_0_32])])).

fof(c_0_65,plain,(
    ! [X12,X13] :
      ( ( ~ v3_pre_topc(X13,X12)
        | r2_hidden(X13,u1_pre_topc(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(X13,u1_pre_topc(X12))
        | v3_pre_topc(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk1_1(X1),u1_pre_topc(X1))
    | v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25])])).

cnf(c_0_68,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_70,plain,
    ( v3_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ v3_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_63]),c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_51]),c_0_44])])).

cnf(c_0_72,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_32]),c_0_41])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(csr,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v3_pre_topc(esk1_1(esk3_0),X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_18])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_32]),c_0_45])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_61]),c_0_76]),c_0_25])])).

cnf(c_0_80,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_32])])).

cnf(c_0_82,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_51]),c_0_25])])).

cnf(c_0_83,plain,
    ( v3_tdlat_3(X1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),esk3_0)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),esk2_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_61]),c_0_76]),c_0_25])]),c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk2_0,X2)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_81]),c_0_82])).

cnf(c_0_88,plain,
    ( v3_tdlat_3(X1)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),esk3_0)
    | ~ m1_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_25])])).

cnf(c_0_90,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),esk2_0)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_51]),c_0_44])])).

cnf(c_0_91,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_32])]),c_0_41]),c_0_79])).

cnf(c_0_92,negated_conjecture,
    ( v3_pre_topc(esk1_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_51]),c_0_44])])).

cnf(c_0_93,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_84]),c_0_92]),c_0_25]),c_0_61]),c_0_45])])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_51])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_39]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.52/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.52/0.74  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.52/0.74  #
% 0.52/0.74  # Preprocessing time       : 0.029 s
% 0.52/0.74  # Presaturation interreduction done
% 0.52/0.74  
% 0.52/0.74  # Proof found!
% 0.52/0.74  # SZS status Theorem
% 0.52/0.74  # SZS output start CNFRefutation
% 0.52/0.74  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.52/0.74  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.52/0.74  fof(t19_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tex_2)).
% 0.52/0.74  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.52/0.74  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.52/0.74  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.52/0.74  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.52/0.74  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.52/0.74  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.52/0.74  fof(d3_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))=>r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tdlat_3)).
% 0.52/0.74  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.52/0.74  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.52/0.74  fof(t33_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 0.52/0.74  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.52/0.74  fof(c_0_14, plain, ![X22, X23]:((~m1_pre_topc(X22,X23)|m1_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))|~l1_pre_topc(X23)|~l1_pre_topc(X22))&(~m1_pre_topc(X22,g1_pre_topc(u1_struct_0(X23),u1_pre_topc(X23)))|m1_pre_topc(X22,X23)|~l1_pre_topc(X23)|~l1_pre_topc(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.52/0.74  fof(c_0_15, plain, ![X14, X15]:(~l1_pre_topc(X14)|(~m1_pre_topc(X15,X14)|l1_pre_topc(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.52/0.74  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&v3_tdlat_3(X1))=>v3_tdlat_3(X2))))), inference(assume_negation,[status(cth)],[t19_tex_2])).
% 0.52/0.74  cnf(c_0_17, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.52/0.74  cnf(c_0_18, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.74  fof(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)&(l1_pre_topc(esk3_0)&((g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))&v3_tdlat_3(esk2_0))&~v3_tdlat_3(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.52/0.74  fof(c_0_20, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.52/0.74  fof(c_0_21, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.52/0.74  fof(c_0_22, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|m1_pre_topc(X21,X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.52/0.74  cnf(c_0_23, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.52/0.74  cnf(c_0_24, negated_conjecture, (g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.74  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.74  cnf(c_0_26, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.74  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.52/0.74  fof(c_0_28, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.52/0.74  fof(c_0_29, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_pre_topc(X29,X28)|m1_subset_1(u1_struct_0(X29),k1_zfmisc_1(u1_struct_0(X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.52/0.74  cnf(c_0_30, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.74  cnf(c_0_31, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.52/0.74  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.74  fof(c_0_33, plain, ![X30]:(~l1_pre_topc(X30)|m1_pre_topc(X30,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.52/0.74  fof(c_0_34, plain, ![X31, X32]:((~v3_tdlat_3(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~r2_hidden(X32,u1_pre_topc(X31))|r2_hidden(k6_subset_1(u1_struct_0(X31),X32),u1_pre_topc(X31))))|~l1_pre_topc(X31))&((m1_subset_1(esk1_1(X31),k1_zfmisc_1(u1_struct_0(X31)))|v3_tdlat_3(X31)|~l1_pre_topc(X31))&((r2_hidden(esk1_1(X31),u1_pre_topc(X31))|v3_tdlat_3(X31)|~l1_pre_topc(X31))&(~r2_hidden(k6_subset_1(u1_struct_0(X31),esk1_1(X31)),u1_pre_topc(X31))|v3_tdlat_3(X31)|~l1_pre_topc(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tdlat_3])])])])])).
% 0.52/0.74  cnf(c_0_35, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.52/0.74  cnf(c_0_36, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.52/0.74  cnf(c_0_37, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.52/0.74  cnf(c_0_38, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.52/0.74  cnf(c_0_39, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.52/0.74  cnf(c_0_40, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.52/0.74  cnf(c_0_41, negated_conjecture, (~v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.74  cnf(c_0_42, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_35, c_0_27])).
% 0.52/0.74  cnf(c_0_43, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_18])).
% 0.52/0.74  cnf(c_0_44, negated_conjecture, (m1_pre_topc(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_25])])).
% 0.52/0.74  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_32]), c_0_41])).
% 0.52/0.74  cnf(c_0_46, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 0.52/0.74  cnf(c_0_47, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_32])])).
% 0.52/0.74  cnf(c_0_48, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_25])])).
% 0.52/0.74  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_45])).
% 0.52/0.74  cnf(c_0_50, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(esk3_0)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X1,esk2_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.52/0.74  cnf(c_0_51, negated_conjecture, (m1_pre_topc(X1,esk2_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_23]), c_0_32])])).
% 0.52/0.74  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_49]), c_0_18])).
% 0.52/0.74  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)|~m1_pre_topc(esk2_0,esk2_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_25])])).
% 0.52/0.74  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,esk3_0)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 0.52/0.74  fof(c_0_55, plain, ![X16]:(~l1_pre_topc(X16)|m1_subset_1(u1_pre_topc(X16),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X16))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.52/0.74  cnf(c_0_56, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)|~m1_pre_topc(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_39]), c_0_25])])).
% 0.52/0.74  fof(c_0_57, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.52/0.74  fof(c_0_58, plain, ![X24, X25, X26, X27]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_pre_topc(X26,X24)|(~v3_pre_topc(X25,X24)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(X27!=X25|v3_pre_topc(X27,X26))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).
% 0.52/0.74  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,esk3_0)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_54]), c_0_18])).
% 0.52/0.74  cnf(c_0_60, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.52/0.74  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk2_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_39]), c_0_32])])).
% 0.52/0.74  cnf(c_0_62, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.52/0.74  cnf(c_0_63, plain, (v3_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.52/0.74  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_39]), c_0_32])])).
% 0.52/0.74  fof(c_0_65, plain, ![X12, X13]:((~v3_pre_topc(X13,X12)|r2_hidden(X13,u1_pre_topc(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~r2_hidden(X13,u1_pre_topc(X12))|v3_pre_topc(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.52/0.74  cnf(c_0_66, plain, (r2_hidden(esk1_1(X1),u1_pre_topc(X1))|v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.52/0.74  cnf(c_0_67, negated_conjecture, (m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_25])])).
% 0.52/0.74  cnf(c_0_68, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.52/0.74  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_62, c_0_60])).
% 0.52/0.74  cnf(c_0_70, plain, (v3_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~v3_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_63]), c_0_36])).
% 0.52/0.74  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_51]), c_0_44])])).
% 0.52/0.74  cnf(c_0_72, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.52/0.74  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_32]), c_0_41])).
% 0.52/0.74  cnf(c_0_74, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(spm,[status(thm)],[c_0_62, c_0_67])).
% 0.52/0.74  cnf(c_0_75, plain, (r2_hidden(k6_subset_1(u1_struct_0(X1),X2),u1_pre_topc(X1))|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(csr,[status(thm)],[c_0_68, c_0_69])).
% 0.52/0.74  cnf(c_0_76, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.52/0.74  cnf(c_0_77, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,X2)|~v3_pre_topc(esk1_1(esk3_0),X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_18])).
% 0.52/0.74  cnf(c_0_78, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_32]), c_0_45])])).
% 0.52/0.74  cnf(c_0_79, negated_conjecture, (m1_subset_1(k6_subset_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_61]), c_0_76]), c_0_25])])).
% 0.52/0.74  cnf(c_0_80, plain, (v3_pre_topc(k6_subset_1(u1_struct_0(X1),X2),X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))|~m1_subset_1(k6_subset_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_72, c_0_75])).
% 0.52/0.74  cnf(c_0_81, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_32])])).
% 0.52/0.74  cnf(c_0_82, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_51]), c_0_25])])).
% 0.52/0.74  cnf(c_0_83, plain, (v3_tdlat_3(X1)|~r2_hidden(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.52/0.74  cnf(c_0_84, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.52/0.74  cnf(c_0_85, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),esk3_0)|~m1_pre_topc(esk3_0,X2)|~v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(spm,[status(thm)],[c_0_70, c_0_79])).
% 0.52/0.74  cnf(c_0_86, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),esk2_0)|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_61]), c_0_76]), c_0_25])]), c_0_79])).
% 0.52/0.74  cnf(c_0_87, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk2_0,X2)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_81]), c_0_82])).
% 0.52/0.74  cnf(c_0_88, plain, (v3_tdlat_3(X1)|~v3_pre_topc(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),X1)|~l1_pre_topc(X1)|~m1_subset_1(k6_subset_1(u1_struct_0(X1),esk1_1(X1)),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.52/0.74  cnf(c_0_89, negated_conjecture, (v3_pre_topc(k6_subset_1(u1_struct_0(esk3_0),X1),esk3_0)|~m1_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,u1_pre_topc(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_25])])).
% 0.52/0.74  cnf(c_0_90, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),esk2_0)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_51]), c_0_44])])).
% 0.52/0.74  cnf(c_0_91, negated_conjecture, (~m1_pre_topc(esk3_0,esk2_0)|~r2_hidden(esk1_1(esk3_0),u1_pre_topc(esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_32])]), c_0_41]), c_0_79])).
% 0.52/0.74  cnf(c_0_92, negated_conjecture, (v3_pre_topc(esk1_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_51]), c_0_44])])).
% 0.52/0.74  cnf(c_0_93, negated_conjecture, (~m1_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_84]), c_0_92]), c_0_25]), c_0_61]), c_0_45])])).
% 0.52/0.74  cnf(c_0_94, negated_conjecture, (~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_93, c_0_51])).
% 0.52/0.74  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_39]), c_0_32])]), ['proof']).
% 0.52/0.74  # SZS output end CNFRefutation
% 0.52/0.74  # Proof object total steps             : 96
% 0.52/0.74  # Proof object clause steps            : 67
% 0.52/0.74  # Proof object formula steps           : 29
% 0.52/0.74  # Proof object conjectures             : 43
% 0.52/0.74  # Proof object clause conjectures      : 40
% 0.52/0.74  # Proof object formula conjectures     : 3
% 0.52/0.74  # Proof object initial clauses used    : 22
% 0.52/0.74  # Proof object initial formulas used   : 14
% 0.52/0.74  # Proof object generating inferences   : 42
% 0.52/0.74  # Proof object simplifying inferences  : 67
% 0.52/0.74  # Training examples: 0 positive, 0 negative
% 0.52/0.74  # Parsed axioms                        : 14
% 0.52/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.74  # Initial clauses                      : 26
% 0.52/0.74  # Removed in clause preprocessing      : 0
% 0.52/0.74  # Initial clauses in saturation        : 26
% 0.52/0.74  # Processed clauses                    : 2287
% 0.52/0.74  # ...of these trivial                  : 3
% 0.52/0.74  # ...subsumed                          : 1490
% 0.52/0.74  # ...remaining for further processing  : 794
% 0.52/0.74  # Other redundant clauses eliminated   : 3
% 0.52/0.74  # Clauses deleted for lack of memory   : 0
% 0.52/0.74  # Backward-subsumed                    : 132
% 0.52/0.74  # Backward-rewritten                   : 9
% 0.52/0.74  # Generated clauses                    : 9168
% 0.52/0.74  # ...of the previous two non-trivial   : 8626
% 0.52/0.74  # Contextual simplify-reflections      : 156
% 0.52/0.74  # Paramodulations                      : 9165
% 0.52/0.74  # Factorizations                       : 0
% 0.52/0.74  # Equation resolutions                 : 3
% 0.52/0.74  # Propositional unsat checks           : 0
% 0.52/0.74  #    Propositional check models        : 0
% 0.52/0.74  #    Propositional check unsatisfiable : 0
% 0.52/0.74  #    Propositional clauses             : 0
% 0.52/0.74  #    Propositional clauses after purity: 0
% 0.52/0.74  #    Propositional unsat core size     : 0
% 0.52/0.74  #    Propositional preprocessing time  : 0.000
% 0.52/0.74  #    Propositional encoding time       : 0.000
% 0.52/0.74  #    Propositional solver time         : 0.000
% 0.52/0.74  #    Success case prop preproc time    : 0.000
% 0.52/0.74  #    Success case prop encoding time   : 0.000
% 0.52/0.74  #    Success case prop solver time     : 0.000
% 0.52/0.74  # Current number of processed clauses  : 626
% 0.52/0.74  #    Positive orientable unit clauses  : 15
% 0.52/0.74  #    Positive unorientable unit clauses: 0
% 0.52/0.74  #    Negative unit clauses             : 3
% 0.52/0.74  #    Non-unit-clauses                  : 608
% 0.52/0.74  # Current number of unprocessed clauses: 6126
% 0.52/0.74  # ...number of literals in the above   : 47751
% 0.52/0.74  # Current number of archived formulas  : 0
% 0.52/0.74  # Current number of archived clauses   : 165
% 0.52/0.74  # Clause-clause subsumption calls (NU) : 181963
% 0.52/0.74  # Rec. Clause-clause subsumption calls : 25353
% 0.52/0.74  # Non-unit clause-clause subsumptions  : 1771
% 0.52/0.74  # Unit Clause-clause subsumption calls : 999
% 0.52/0.74  # Rewrite failures with RHS unbound    : 0
% 0.52/0.74  # BW rewrite match attempts            : 4
% 0.52/0.74  # BW rewrite match successes           : 3
% 0.52/0.74  # Condensation attempts                : 0
% 0.52/0.74  # Condensation successes               : 0
% 0.52/0.74  # Termbank termtop insertions          : 647200
% 0.52/0.74  
% 0.52/0.74  # -------------------------------------------------
% 0.52/0.74  # User time                : 0.378 s
% 0.52/0.74  # System time              : 0.016 s
% 0.52/0.74  # Total time               : 0.394 s
% 0.52/0.74  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
