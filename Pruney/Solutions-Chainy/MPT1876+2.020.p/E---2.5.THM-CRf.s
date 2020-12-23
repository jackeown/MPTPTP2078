%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:18 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  104 (1392 expanded)
%              Number of clauses        :   61 ( 574 expanded)
%              Number of leaves         :   21 ( 346 expanded)
%              Depth                    :   22
%              Number of atoms          :  349 (5850 expanded)
%              Number of equality atoms :   37 ( 534 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   35 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(t34_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & v1_tdlat_3(X3)
                    & m1_pre_topc(X3,X1) )
                 => X2 != u1_struct_0(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(cc32_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & ~ v7_struct_0(X2) )
           => ( ~ v2_struct_0(X2)
              & ~ v1_tdlat_3(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tex_2])).

fof(c_0_22,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k3_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k3_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X21,X22] : k4_xboole_0(X21,k4_xboole_0(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_24,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v2_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v2_tex_2(esk5_0,esk4_0)
      | ~ v1_zfmisc_1(esk5_0) )
    & ( v2_tex_2(esk5_0,esk4_0)
      | v1_zfmisc_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(X18,X19) != k1_xboole_0
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | k4_xboole_0(X18,X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk5_0,u1_struct_0(esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_38,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_39,plain,(
    ! [X37,X38] :
      ( v1_xboole_0(X37)
      | ~ m1_subset_1(X38,X37)
      | k6_domain_1(X37,X38) = k1_tarski(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_40,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_41,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | m1_subset_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_45,plain,(
    ! [X27,X28] :
      ( ~ v1_xboole_0(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | v1_xboole_0(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_46,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(k1_tarski(X25),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_30]),c_0_44])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k2_tarski(esk1_1(esk5_0),esk1_1(esk5_0)) = k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

fof(c_0_58,plain,(
    ! [X24] : ~ v1_xboole_0(k1_tarski(X24)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)),k1_zfmisc_1(X1))
    | ~ r2_hidden(esk1_1(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_61,plain,(
    ! [X42,X43] :
      ( v1_xboole_0(X42)
      | v1_xboole_0(X43)
      | ~ v1_zfmisc_1(X43)
      | ~ r1_tarski(X42,X43)
      | X42 = X43 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)),k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_43]),c_0_44])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_48])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

fof(c_0_67,plain,(
    ! [X47,X48] :
      ( v2_struct_0(X47)
      | ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | v2_tex_2(k6_domain_1(u1_struct_0(X47),X48),X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_68,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)) = esk5_0
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_44]),c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_70,plain,(
    ! [X44,X45] :
      ( ( ~ v2_struct_0(esk3_2(X44,X45))
        | ~ v2_tex_2(X45,X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( v1_pre_topc(esk3_2(X44,X45))
        | ~ v2_tex_2(X45,X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( v1_tdlat_3(esk3_2(X44,X45))
        | ~ v2_tex_2(X45,X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( m1_pre_topc(esk3_2(X44,X45),X44)
        | ~ v2_tex_2(X45,X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) )
      & ( X45 = u1_struct_0(esk3_2(X44,X45))
        | ~ v2_tex_2(X45,X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | v2_struct_0(X44)
        | ~ v2_pre_topc(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)) = esk5_0
    | v2_tex_2(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_76,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_pre_topc(X35,X34)
      | l1_pre_topc(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_77,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_54])]),c_0_75])).

fof(c_0_79,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | l1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_80,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_73]),c_0_74]),c_0_30])]),c_0_75]),c_0_44])).

fof(c_0_82,plain,(
    ! [X40,X41] :
      ( ( ~ v2_struct_0(X41)
        | v2_struct_0(X41)
        | v7_struct_0(X41)
        | ~ m1_pre_topc(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v2_tdlat_3(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ v1_tdlat_3(X41)
        | v2_struct_0(X41)
        | v7_struct_0(X41)
        | ~ m1_pre_topc(X41,X40)
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ v2_tdlat_3(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).

fof(c_0_83,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | ~ v2_tdlat_3(X39)
      | v2_pre_topc(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

fof(c_0_84,plain,(
    ! [X36] :
      ( ~ v7_struct_0(X36)
      | ~ l1_struct_0(X36)
      | v1_zfmisc_1(u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_85,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_86,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0)
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_87,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( l1_pre_topc(esk3_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_74])])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_91,plain,
    ( v1_tdlat_3(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_92,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(esk3_2(esk4_0,esk5_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_78]),c_0_73]),c_0_74]),c_0_30])]),c_0_75]),c_0_44])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_zfmisc_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_78])])).

cnf(c_0_95,negated_conjecture,
    ( l1_struct_0(esk3_2(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( v1_tdlat_3(esk3_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_78]),c_0_73]),c_0_74]),c_0_30])]),c_0_75]),c_0_44])).

cnf(c_0_98,negated_conjecture,
    ( ~ v7_struct_0(esk3_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_95])])).

cnf(c_0_99,negated_conjecture,
    ( v2_struct_0(esk3_2(esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_pre_topc(esk3_2(esk4_0,esk5_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( v2_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_101,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_102,negated_conjecture,
    ( v2_struct_0(esk3_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_81]),c_0_100]),c_0_74])]),c_0_75])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_78]),c_0_73]),c_0_74]),c_0_30])]),c_0_75]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.61/0.77  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.61/0.77  # and selection function PSelectComplexPreferEQ.
% 0.61/0.77  #
% 0.61/0.77  # Preprocessing time       : 0.029 s
% 0.61/0.77  # Presaturation interreduction done
% 0.61/0.77  
% 0.61/0.77  # Proof found!
% 0.61/0.77  # SZS status Theorem
% 0.61/0.77  # SZS output start CNFRefutation
% 0.61/0.77  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.61/0.77  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.61/0.77  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.61/0.77  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.61/0.77  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.61/0.77  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.61/0.77  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.61/0.77  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.61/0.77  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.61/0.77  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.61/0.77  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.61/0.77  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.61/0.77  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.61/0.77  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.61/0.77  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.61/0.77  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.61/0.77  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.61/0.77  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.61/0.77  fof(cc32_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((~(v2_struct_0(X2))&~(v7_struct_0(X2)))=>(~(v2_struct_0(X2))&~(v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 0.61/0.77  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.61/0.77  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.61/0.77  fof(c_0_21, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.61/0.77  fof(c_0_22, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:((((r2_hidden(X12,X9)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10))&(r2_hidden(X12,X10)|~r2_hidden(X12,X11)|X11!=k3_xboole_0(X9,X10)))&(~r2_hidden(X13,X9)|~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k3_xboole_0(X9,X10)))&((~r2_hidden(esk2_3(X14,X15,X16),X16)|(~r2_hidden(esk2_3(X14,X15,X16),X14)|~r2_hidden(esk2_3(X14,X15,X16),X15))|X16=k3_xboole_0(X14,X15))&((r2_hidden(esk2_3(X14,X15,X16),X14)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))&(r2_hidden(esk2_3(X14,X15,X16),X15)|r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k3_xboole_0(X14,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.61/0.77  fof(c_0_23, plain, ![X21, X22]:k4_xboole_0(X21,k4_xboole_0(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.61/0.77  fof(c_0_24, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.61/0.77  fof(c_0_25, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v2_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0))&(v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.61/0.77  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.61/0.77  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.77  fof(c_0_28, plain, ![X18, X19]:((k4_xboole_0(X18,X19)!=k1_xboole_0|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|k4_xboole_0(X18,X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.61/0.77  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.61/0.77  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.61/0.77  cnf(c_0_32, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.61/0.77  cnf(c_0_33, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.61/0.77  fof(c_0_34, plain, ![X20]:k4_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.61/0.77  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_31])).
% 0.61/0.77  cnf(c_0_36, negated_conjecture, (k4_xboole_0(esk5_0,u1_struct_0(esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.61/0.77  cnf(c_0_37, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.61/0.77  fof(c_0_38, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.61/0.77  fof(c_0_39, plain, ![X37, X38]:(v1_xboole_0(X37)|~m1_subset_1(X38,X37)|k6_domain_1(X37,X38)=k1_tarski(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.61/0.77  fof(c_0_40, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.61/0.77  fof(c_0_41, plain, ![X29, X30]:(~r2_hidden(X29,X30)|m1_subset_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.61/0.77  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.61/0.77  cnf(c_0_43, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.61/0.77  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  fof(c_0_45, plain, ![X27, X28]:(~v1_xboole_0(X27)|(~m1_subset_1(X28,k1_zfmisc_1(X27))|v1_xboole_0(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.61/0.77  fof(c_0_46, plain, ![X25, X26]:(~r2_hidden(X25,X26)|m1_subset_1(k1_tarski(X25),k1_zfmisc_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.61/0.77  cnf(c_0_47, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.61/0.77  cnf(c_0_48, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.61/0.77  cnf(c_0_49, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.61/0.77  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_1(esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.61/0.77  cnf(c_0_51, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.61/0.77  cnf(c_0_52, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.61/0.77  cnf(c_0_53, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.61/0.77  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk1_1(esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.61/0.77  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_30]), c_0_44])).
% 0.61/0.77  cnf(c_0_56, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_52, c_0_48])).
% 0.61/0.77  cnf(c_0_57, negated_conjecture, (k2_tarski(esk1_1(esk5_0),esk1_1(esk5_0))=k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.61/0.77  fof(c_0_58, plain, ![X24]:~v1_xboole_0(k1_tarski(X24)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.61/0.77  cnf(c_0_59, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)),k1_zfmisc_1(X1))|~r2_hidden(esk1_1(esk5_0),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.61/0.77  cnf(c_0_60, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.61/0.77  fof(c_0_61, plain, ![X42, X43]:(v1_xboole_0(X42)|(v1_xboole_0(X43)|~v1_zfmisc_1(X43)|(~r1_tarski(X42,X43)|X42=X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.61/0.77  cnf(c_0_62, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)),k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_43]), c_0_44])).
% 0.61/0.77  cnf(c_0_63, plain, (~v1_xboole_0(k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_60, c_0_48])).
% 0.61/0.77  cnf(c_0_64, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.61/0.77  cnf(c_0_65, negated_conjecture, (r1_tarski(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_62])).
% 0.61/0.77  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0)))), inference(spm,[status(thm)],[c_0_63, c_0_57])).
% 0.61/0.77  fof(c_0_67, plain, ![X47, X48]:(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)|(~m1_subset_1(X48,u1_struct_0(X47))|v2_tex_2(k6_domain_1(u1_struct_0(X47),X48),X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.61/0.77  cnf(c_0_68, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0))=esk5_0|~v1_zfmisc_1(esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_44]), c_0_66])).
% 0.61/0.77  cnf(c_0_69, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  fof(c_0_70, plain, ![X44, X45]:(((((~v2_struct_0(esk3_2(X44,X45))|~v2_tex_2(X45,X44)|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))&(v1_pre_topc(esk3_2(X44,X45))|~v2_tex_2(X45,X44)|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(v1_tdlat_3(esk3_2(X44,X45))|~v2_tex_2(X45,X44)|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(m1_pre_topc(esk3_2(X44,X45),X44)|~v2_tex_2(X45,X44)|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44))))&(X45=u1_struct_0(esk3_2(X44,X45))|~v2_tex_2(X45,X44)|(v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44))))|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.61/0.77  cnf(c_0_71, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.61/0.77  cnf(c_0_72, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk5_0))=esk5_0|v2_tex_2(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.61/0.77  cnf(c_0_73, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  cnf(c_0_74, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  cnf(c_0_75, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  fof(c_0_76, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_pre_topc(X35,X34)|l1_pre_topc(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.61/0.77  cnf(c_0_77, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.61/0.77  cnf(c_0_78, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74]), c_0_54])]), c_0_75])).
% 0.61/0.77  fof(c_0_79, plain, ![X33]:(~l1_pre_topc(X33)|l1_struct_0(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.61/0.77  cnf(c_0_80, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.61/0.77  cnf(c_0_81, negated_conjecture, (m1_pre_topc(esk3_2(esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_73]), c_0_74]), c_0_30])]), c_0_75]), c_0_44])).
% 0.61/0.77  fof(c_0_82, plain, ![X40, X41]:((~v2_struct_0(X41)|(v2_struct_0(X41)|v7_struct_0(X41))|~m1_pre_topc(X41,X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v2_tdlat_3(X40)|~l1_pre_topc(X40)))&(~v1_tdlat_3(X41)|(v2_struct_0(X41)|v7_struct_0(X41))|~m1_pre_topc(X41,X40)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~v2_tdlat_3(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).
% 0.61/0.77  fof(c_0_83, plain, ![X39]:(~l1_pre_topc(X39)|(~v2_tdlat_3(X39)|v2_pre_topc(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.61/0.77  fof(c_0_84, plain, ![X36]:(~v7_struct_0(X36)|~l1_struct_0(X36)|v1_zfmisc_1(u1_struct_0(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.61/0.77  cnf(c_0_85, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.61/0.77  cnf(c_0_86, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  cnf(c_0_87, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.61/0.77  cnf(c_0_88, negated_conjecture, (l1_pre_topc(esk3_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_74])])).
% 0.61/0.77  cnf(c_0_89, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v2_struct_0(X2)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.61/0.77  cnf(c_0_90, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.61/0.77  cnf(c_0_91, plain, (v1_tdlat_3(esk3_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.61/0.77  cnf(c_0_92, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.61/0.77  cnf(c_0_93, negated_conjecture, (u1_struct_0(esk3_2(esk4_0,esk5_0))=esk5_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_78]), c_0_73]), c_0_74]), c_0_30])]), c_0_75]), c_0_44])).
% 0.61/0.77  cnf(c_0_94, negated_conjecture, (~v1_zfmisc_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_78])])).
% 0.61/0.77  cnf(c_0_95, negated_conjecture, (l1_struct_0(esk3_2(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.61/0.77  cnf(c_0_96, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_89, c_0_90])).
% 0.61/0.77  cnf(c_0_97, negated_conjecture, (v1_tdlat_3(esk3_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_78]), c_0_73]), c_0_74]), c_0_30])]), c_0_75]), c_0_44])).
% 0.61/0.77  cnf(c_0_98, negated_conjecture, (~v7_struct_0(esk3_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_95])])).
% 0.61/0.77  cnf(c_0_99, negated_conjecture, (v2_struct_0(esk3_2(esk4_0,esk5_0))|v2_struct_0(X1)|~v2_tdlat_3(X1)|~m1_pre_topc(esk3_2(esk4_0,esk5_0),X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])).
% 0.61/0.77  cnf(c_0_100, negated_conjecture, (v2_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.61/0.77  cnf(c_0_101, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.61/0.77  cnf(c_0_102, negated_conjecture, (v2_struct_0(esk3_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_81]), c_0_100]), c_0_74])]), c_0_75])).
% 0.61/0.77  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_78]), c_0_73]), c_0_74]), c_0_30])]), c_0_75]), c_0_44]), ['proof']).
% 0.61/0.77  # SZS output end CNFRefutation
% 0.61/0.77  # Proof object total steps             : 104
% 0.61/0.77  # Proof object clause steps            : 61
% 0.61/0.77  # Proof object formula steps           : 43
% 0.61/0.77  # Proof object conjectures             : 35
% 0.61/0.77  # Proof object clause conjectures      : 32
% 0.61/0.77  # Proof object formula conjectures     : 3
% 0.61/0.77  # Proof object initial clauses used    : 31
% 0.61/0.77  # Proof object initial formulas used   : 21
% 0.61/0.77  # Proof object generating inferences   : 23
% 0.61/0.77  # Proof object simplifying inferences  : 55
% 0.61/0.77  # Training examples: 0 positive, 0 negative
% 0.61/0.77  # Parsed axioms                        : 21
% 0.61/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.77  # Initial clauses                      : 41
% 0.61/0.77  # Removed in clause preprocessing      : 3
% 0.61/0.77  # Initial clauses in saturation        : 38
% 0.61/0.77  # Processed clauses                    : 1118
% 0.61/0.77  # ...of these trivial                  : 27
% 0.61/0.77  # ...subsumed                          : 512
% 0.61/0.77  # ...remaining for further processing  : 579
% 0.61/0.77  # Other redundant clauses eliminated   : 31
% 0.61/0.77  # Clauses deleted for lack of memory   : 0
% 0.61/0.77  # Backward-subsumed                    : 28
% 0.61/0.77  # Backward-rewritten                   : 29
% 0.61/0.77  # Generated clauses                    : 22635
% 0.61/0.77  # ...of the previous two non-trivial   : 22044
% 0.61/0.77  # Contextual simplify-reflections      : 22
% 0.61/0.77  # Paramodulations                      : 22428
% 0.61/0.77  # Factorizations                       : 176
% 0.61/0.77  # Equation resolutions                 : 31
% 0.61/0.77  # Propositional unsat checks           : 0
% 0.61/0.77  #    Propositional check models        : 0
% 0.61/0.77  #    Propositional check unsatisfiable : 0
% 0.61/0.77  #    Propositional clauses             : 0
% 0.61/0.77  #    Propositional clauses after purity: 0
% 0.61/0.77  #    Propositional unsat core size     : 0
% 0.61/0.77  #    Propositional preprocessing time  : 0.000
% 0.61/0.77  #    Propositional encoding time       : 0.000
% 0.61/0.77  #    Propositional solver time         : 0.000
% 0.61/0.77  #    Success case prop preproc time    : 0.000
% 0.61/0.77  #    Success case prop encoding time   : 0.000
% 0.61/0.77  #    Success case prop solver time     : 0.000
% 0.61/0.77  # Current number of processed clauses  : 481
% 0.61/0.77  #    Positive orientable unit clauses  : 71
% 0.61/0.77  #    Positive unorientable unit clauses: 0
% 0.61/0.77  #    Negative unit clauses             : 10
% 0.61/0.77  #    Non-unit-clauses                  : 400
% 0.61/0.77  # Current number of unprocessed clauses: 20943
% 0.61/0.77  # ...number of literals in the above   : 116004
% 0.61/0.77  # Current number of archived formulas  : 0
% 0.61/0.77  # Current number of archived clauses   : 97
% 0.61/0.77  # Clause-clause subsumption calls (NU) : 33830
% 0.61/0.77  # Rec. Clause-clause subsumption calls : 12821
% 0.61/0.77  # Non-unit clause-clause subsumptions  : 476
% 0.61/0.77  # Unit Clause-clause subsumption calls : 136
% 0.61/0.77  # Rewrite failures with RHS unbound    : 0
% 0.61/0.77  # BW rewrite match attempts            : 31
% 0.61/0.77  # BW rewrite match successes           : 5
% 0.61/0.77  # Condensation attempts                : 0
% 0.61/0.77  # Condensation successes               : 0
% 0.61/0.77  # Termbank termtop insertions          : 538903
% 0.61/0.77  
% 0.61/0.77  # -------------------------------------------------
% 0.61/0.77  # User time                : 0.412 s
% 0.61/0.77  # System time              : 0.020 s
% 0.61/0.77  # Total time               : 0.432 s
% 0.61/0.77  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
