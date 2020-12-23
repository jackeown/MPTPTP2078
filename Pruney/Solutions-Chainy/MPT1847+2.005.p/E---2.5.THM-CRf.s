%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:18 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 680 expanded)
%              Number of clauses        :   73 ( 260 expanded)
%              Number of leaves         :   16 ( 168 expanded)
%              Depth                    :   14
%              Number of atoms          :  303 (2814 expanded)
%              Number of equality atoms :   43 ( 403 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

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
    ! [X26,X27,X28] :
      ( ( ~ v1_tex_2(X27,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))
        | X28 != u1_struct_0(X27)
        | v1_subset_1(X28,u1_struct_0(X26))
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk1_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))
        | v1_tex_2(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( esk1_2(X26,X27) = u1_struct_0(X27)
        | v1_tex_2(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v1_subset_1(esk1_2(X26,X27),u1_struct_0(X26))
        | v1_tex_2(X27,X26)
        | ~ m1_pre_topc(X27,X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    & v1_tex_2(esk3_0,esk2_0)
    & ~ v1_tex_2(esk4_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | l1_pre_topc(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,plain,(
    ! [X9,X10,X11] :
      ( ( X11 != k1_pre_topc(X9,X10)
        | k2_struct_0(X11) = X10
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( k2_struct_0(X11) != X10
        | X11 = k1_pre_topc(X9,X10)
        | ~ v1_pre_topc(X11)
        | ~ m1_pre_topc(X11,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ( v1_pre_topc(k1_pre_topc(X13,X14))
        | ~ l1_pre_topc(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13))) )
      & ( m1_pre_topc(k1_pre_topc(X13,X14),X13)
        | ~ l1_pre_topc(X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_22,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_tex_2(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
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

fof(c_0_27,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | r1_tarski(u1_struct_0(X25),u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_30,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_31,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | m1_subset_1(u1_struct_0(X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
      | m1_pre_topc(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_36,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk4_0) = esk1_2(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24])])).

fof(c_0_42,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_46,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) = g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_38]),c_0_24])])).

cnf(c_0_50,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_41])])).

cnf(c_0_52,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk4_0,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_2(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_37]),c_0_41])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(esk1_2(esk2_0,esk4_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_37]),c_0_41])])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_57,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_37]),c_0_41])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),esk1_2(esk2_0,esk4_0))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k2_struct_0(k1_pre_topc(X1,u1_struct_0(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_41])])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_49])])).

cnf(c_0_62,plain,
    ( r1_tarski(k2_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk4_0,u1_struct_0(X1))) = u1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X2)),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_46])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))
    | ~ l1_struct_0(k1_pre_topc(X1,u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X1)),esk4_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(k1_pre_topc(esk4_0,u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(X1)),X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(X1)),esk3_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_41])])).

fof(c_0_70,plain,(
    ! [X30,X31] :
      ( ( ~ v1_subset_1(X31,X30)
        | X31 != X30
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) )
      & ( X31 = X30
        | v1_subset_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_71,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))
    | ~ l1_struct_0(k1_pre_topc(X1,u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X1)),esk3_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X1)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_53])).

fof(c_0_74,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_67]),c_0_41])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ l1_struct_0(k1_pre_topc(esk4_0,u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_49])])).

cnf(c_0_77,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk4_0,X1),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_2(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_41])])).

cnf(c_0_78,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk1_2(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_23]),c_0_24])]),c_0_25])).

fof(c_0_80,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),esk1_2(esk2_0,esk4_0))
    | ~ l1_struct_0(k1_pre_topc(esk3_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_49])])).

cnf(c_0_82,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk3_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_73]),c_0_49])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k2_struct_0(X1),u1_struct_0(esk3_0))
    | ~ l1_struct_0(k1_pre_topc(esk4_0,k2_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_52])).

cnf(c_0_85,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0))) = esk1_2(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_86,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_37]),c_0_41])])).

cnf(c_0_87,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_2(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_77]),c_0_41])])).

cnf(c_0_88,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_89,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_90,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk1_2(esk2_0,esk4_0)
    | v1_subset_1(esk1_2(esk2_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),esk1_2(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(esk1_2(esk2_0,esk4_0),u1_struct_0(esk3_0))
    | ~ l1_struct_0(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86])])).

cnf(c_0_94,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_53])).

fof(c_0_95,plain,(
    ! [X8] : ~ v1_subset_1(k2_subset_1(X8),X8) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

cnf(c_0_96,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_88]),c_0_46])).

cnf(c_0_97,negated_conjecture,
    ( u1_struct_0(esk2_0) = esk1_2(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_98,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk1_2(esk2_0,esk4_0)
    | ~ r1_tarski(esk1_2(esk2_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk1_2(esk2_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_82]),c_0_94])])).

cnf(c_0_100,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( v1_subset_1(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))
    | ~ v1_tex_2(X1,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_24])])).

cnf(c_0_102,negated_conjecture,
    ( u1_struct_0(esk3_0) = esk1_2(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])])).

cnf(c_0_103,negated_conjecture,
    ( v1_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_104,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_100,c_0_44])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_38])]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.52  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S06DN
% 0.21/0.52  # and selection function SelectNewComplexAHPExceptUniqMaxHorn.
% 0.21/0.52  #
% 0.21/0.52  # Preprocessing time       : 0.028 s
% 0.21/0.52  # Presaturation interreduction done
% 0.21/0.52  
% 0.21/0.52  # Proof found!
% 0.21/0.52  # SZS status Theorem
% 0.21/0.52  # SZS output start CNFRefutation
% 0.21/0.52  fof(t14_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tex_2)).
% 0.21/0.52  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 0.21/0.52  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.52  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.21/0.52  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.21/0.52  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.21/0.52  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.21/0.52  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.21/0.52  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.21/0.52  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.52  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.21/0.52  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.52  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 0.21/0.52  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.52  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.21/0.52  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1)))))), inference(assume_negation,[status(cth)],[t14_tex_2])).
% 0.21/0.52  fof(c_0_17, plain, ![X26, X27, X28]:((~v1_tex_2(X27,X26)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X26)))|(X28!=u1_struct_0(X27)|v1_subset_1(X28,u1_struct_0(X26))))|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&((m1_subset_1(esk1_2(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))|v1_tex_2(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&((esk1_2(X26,X27)=u1_struct_0(X27)|v1_tex_2(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))&(~v1_subset_1(esk1_2(X26,X27),u1_struct_0(X26))|v1_tex_2(X27,X26)|~m1_pre_topc(X27,X26)|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.21/0.52  fof(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(m1_pre_topc(esk4_0,esk2_0)&((g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))&v1_tex_2(esk3_0,esk2_0))&~v1_tex_2(esk4_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.21/0.52  fof(c_0_19, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|l1_pre_topc(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.52  fof(c_0_20, plain, ![X9, X10, X11]:((X11!=k1_pre_topc(X9,X10)|k2_struct_0(X11)=X10|(~v1_pre_topc(X11)|~m1_pre_topc(X11,X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))&(k2_struct_0(X11)!=X10|X11=k1_pre_topc(X9,X10)|(~v1_pre_topc(X11)|~m1_pre_topc(X11,X9))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|~l1_pre_topc(X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.21/0.52  fof(c_0_21, plain, ![X13, X14]:((v1_pre_topc(k1_pre_topc(X13,X14))|(~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))))&(m1_pre_topc(k1_pre_topc(X13,X14),X13)|(~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.21/0.52  cnf(c_0_22, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  cnf(c_0_25, negated_conjecture, (~v1_tex_2(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  fof(c_0_26, plain, ![X20, X21]:((~m1_pre_topc(X20,X21)|m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(~m1_pre_topc(X20,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|m1_pre_topc(X20,X21)|~l1_pre_topc(X21)|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.21/0.52  fof(c_0_27, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|r1_tarski(u1_struct_0(X25),u1_struct_0(X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.21/0.52  cnf(c_0_28, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.52  fof(c_0_29, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.21/0.52  fof(c_0_30, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.21/0.52  cnf(c_0_31, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.52  cnf(c_0_32, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.52  cnf(c_0_33, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.52  fof(c_0_34, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|m1_subset_1(u1_struct_0(X23),k1_zfmisc_1(u1_struct_0(X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.52  fof(c_0_35, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|m1_pre_topc(X19,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.21/0.52  cnf(c_0_36, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  cnf(c_0_37, negated_conjecture, (u1_struct_0(esk4_0)=esk1_2(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), c_0_25])).
% 0.21/0.52  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  cnf(c_0_39, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.52  cnf(c_0_40, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.52  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_24])])).
% 0.21/0.52  fof(c_0_42, plain, ![X12]:(~l1_struct_0(X12)|k2_struct_0(X12)=u1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.52  cnf(c_0_43, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.52  cnf(c_0_44, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.52  cnf(c_0_45, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]), c_0_32]), c_0_33])).
% 0.21/0.52  cnf(c_0_46, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.52  cnf(c_0_47, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.52  cnf(c_0_48, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))=g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.52  cnf(c_0_49, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_38]), c_0_24])])).
% 0.21/0.52  cnf(c_0_50, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_39, c_0_28])).
% 0.21/0.52  cnf(c_0_51, negated_conjecture, (r1_tarski(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_41])])).
% 0.21/0.52  cnf(c_0_52, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.52  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.52  cnf(c_0_54, negated_conjecture, (k2_struct_0(k1_pre_topc(esk4_0,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(esk1_2(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_37]), c_0_41])])).
% 0.21/0.52  cnf(c_0_55, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(esk1_2(esk2_0,esk4_0)))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_37]), c_0_41])])).
% 0.21/0.52  cnf(c_0_56, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.21/0.52  cnf(c_0_57, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0)))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_37]), c_0_41])])).
% 0.21/0.52  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_struct_0(X1),esk1_2(esk2_0,esk4_0))|~l1_struct_0(X1)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.52  cnf(c_0_59, plain, (k2_struct_0(k1_pre_topc(X1,u1_struct_0(X1)))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_53])).
% 0.21/0.52  cnf(c_0_60, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_37]), c_0_41])])).
% 0.21/0.52  cnf(c_0_61, negated_conjecture, (m1_pre_topc(X1,g1_pre_topc(esk1_2(esk2_0,esk4_0),u1_pre_topc(esk4_0)))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_49])])).
% 0.21/0.52  cnf(c_0_62, plain, (r1_tarski(k2_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 0.21/0.52  cnf(c_0_63, negated_conjecture, (k2_struct_0(k1_pre_topc(esk4_0,u1_struct_0(X1)))=u1_struct_0(X1)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.52  cnf(c_0_64, negated_conjecture, (m1_pre_topc(X1,esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.52  cnf(c_0_65, plain, (m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X2)),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_46])).
% 0.21/0.52  cnf(c_0_66, negated_conjecture, (r1_tarski(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))|~l1_struct_0(k1_pre_topc(X1,u1_struct_0(X1)))|~m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X1)),esk4_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.52  cnf(c_0_67, negated_conjecture, (m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.52  cnf(c_0_68, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(k1_pre_topc(esk4_0,u1_struct_0(X1)))|~m1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(X1)),X2)|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.52  cnf(c_0_69, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk4_0,u1_struct_0(X1)),esk3_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_41])])).
% 0.21/0.52  fof(c_0_70, plain, ![X30, X31]:((~v1_subset_1(X31,X30)|X31!=X30|~m1_subset_1(X31,k1_zfmisc_1(X30)))&(X31=X30|v1_subset_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.21/0.52  cnf(c_0_71, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  cnf(c_0_72, negated_conjecture, (r1_tarski(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))|~l1_struct_0(k1_pre_topc(X1,u1_struct_0(X1)))|~m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X1)),esk3_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.52  cnf(c_0_73, plain, (m1_pre_topc(k1_pre_topc(X1,u1_struct_0(X1)),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_53])).
% 0.21/0.52  fof(c_0_74, plain, ![X15]:(~l1_pre_topc(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.52  cnf(c_0_75, negated_conjecture, (l1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_67]), c_0_41])])).
% 0.21/0.52  cnf(c_0_76, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk3_0))|~l1_struct_0(k1_pre_topc(esk4_0,u1_struct_0(X1)))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_49])])).
% 0.21/0.52  cnf(c_0_77, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk4_0,X1),esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(esk1_2(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_41])])).
% 0.21/0.52  cnf(c_0_78, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.52  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk1_2(esk2_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_23]), c_0_24])]), c_0_25])).
% 0.21/0.52  fof(c_0_80, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.52  cnf(c_0_81, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),esk1_2(esk2_0,esk4_0))|~l1_struct_0(k1_pre_topc(esk3_0,u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_49])])).
% 0.21/0.52  cnf(c_0_82, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.21/0.52  cnf(c_0_83, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk3_0,u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_73]), c_0_49])])).
% 0.21/0.52  cnf(c_0_84, negated_conjecture, (r1_tarski(k2_struct_0(X1),u1_struct_0(esk3_0))|~l1_struct_0(k1_pre_topc(esk4_0,k2_struct_0(X1)))|~l1_struct_0(X1)|~m1_pre_topc(X1,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_52])).
% 0.21/0.52  cnf(c_0_85, negated_conjecture, (k2_struct_0(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0)))=esk1_2(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_53])).
% 0.21/0.52  cnf(c_0_86, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_37]), c_0_41])])).
% 0.21/0.52  cnf(c_0_87, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(esk1_2(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_77]), c_0_41])])).
% 0.21/0.52  cnf(c_0_88, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  cnf(c_0_89, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.52  cnf(c_0_90, negated_conjecture, (u1_struct_0(esk2_0)=esk1_2(esk2_0,esk4_0)|v1_subset_1(esk1_2(esk2_0,esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.52  cnf(c_0_91, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.21/0.52  cnf(c_0_92, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),esk1_2(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])])).
% 0.21/0.52  cnf(c_0_93, negated_conjecture, (r1_tarski(esk1_2(esk2_0,esk4_0),u1_struct_0(esk3_0))|~l1_struct_0(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86])])).
% 0.21/0.52  cnf(c_0_94, negated_conjecture, (l1_pre_topc(k1_pre_topc(esk4_0,esk1_2(esk2_0,esk4_0)))), inference(spm,[status(thm)],[c_0_87, c_0_53])).
% 0.21/0.52  fof(c_0_95, plain, ![X8]:~v1_subset_1(k2_subset_1(X8),X8), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.21/0.52  cnf(c_0_96, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_88]), c_0_46])).
% 0.21/0.52  cnf(c_0_97, negated_conjecture, (u1_struct_0(esk2_0)=esk1_2(esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_23]), c_0_24])]), c_0_25])).
% 0.21/0.52  cnf(c_0_98, negated_conjecture, (u1_struct_0(esk3_0)=esk1_2(esk2_0,esk4_0)|~r1_tarski(esk1_2(esk2_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.21/0.52  cnf(c_0_99, negated_conjecture, (r1_tarski(esk1_2(esk2_0,esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_82]), c_0_94])])).
% 0.21/0.52  cnf(c_0_100, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.21/0.52  cnf(c_0_101, negated_conjecture, (v1_subset_1(u1_struct_0(X1),esk1_2(esk2_0,esk4_0))|~v1_tex_2(X1,esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_24])])).
% 0.21/0.52  cnf(c_0_102, negated_conjecture, (u1_struct_0(esk3_0)=esk1_2(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])])).
% 0.21/0.52  cnf(c_0_103, negated_conjecture, (v1_tex_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.52  cnf(c_0_104, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_100, c_0_44])).
% 0.21/0.52  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_38])]), c_0_104]), ['proof']).
% 0.21/0.52  # SZS output end CNFRefutation
% 0.21/0.52  # Proof object total steps             : 106
% 0.21/0.52  # Proof object clause steps            : 73
% 0.21/0.52  # Proof object formula steps           : 33
% 0.21/0.52  # Proof object conjectures             : 48
% 0.21/0.52  # Proof object clause conjectures      : 45
% 0.21/0.52  # Proof object formula conjectures     : 3
% 0.21/0.52  # Proof object initial clauses used    : 25
% 0.21/0.52  # Proof object initial formulas used   : 16
% 0.21/0.52  # Proof object generating inferences   : 41
% 0.21/0.52  # Proof object simplifying inferences  : 67
% 0.21/0.52  # Training examples: 0 positive, 0 negative
% 0.21/0.52  # Parsed axioms                        : 16
% 0.21/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.52  # Initial clauses                      : 30
% 0.21/0.52  # Removed in clause preprocessing      : 1
% 0.21/0.52  # Initial clauses in saturation        : 29
% 0.21/0.52  # Processed clauses                    : 1347
% 0.21/0.52  # ...of these trivial                  : 7
% 0.21/0.52  # ...subsumed                          : 677
% 0.21/0.52  # ...remaining for further processing  : 663
% 0.21/0.52  # Other redundant clauses eliminated   : 6
% 0.21/0.52  # Clauses deleted for lack of memory   : 0
% 0.21/0.52  # Backward-subsumed                    : 35
% 0.21/0.52  # Backward-rewritten                   : 80
% 0.21/0.52  # Generated clauses                    : 5794
% 0.21/0.52  # ...of the previous two non-trivial   : 4551
% 0.21/0.52  # Contextual simplify-reflections      : 85
% 0.21/0.52  # Paramodulations                      : 5788
% 0.21/0.52  # Factorizations                       : 0
% 0.21/0.52  # Equation resolutions                 : 6
% 0.21/0.52  # Propositional unsat checks           : 0
% 0.21/0.52  #    Propositional check models        : 0
% 0.21/0.52  #    Propositional check unsatisfiable : 0
% 0.21/0.52  #    Propositional clauses             : 0
% 0.21/0.52  #    Propositional clauses after purity: 0
% 0.21/0.52  #    Propositional unsat core size     : 0
% 0.21/0.52  #    Propositional preprocessing time  : 0.000
% 0.21/0.52  #    Propositional encoding time       : 0.000
% 0.21/0.52  #    Propositional solver time         : 0.000
% 0.21/0.52  #    Success case prop preproc time    : 0.000
% 0.21/0.52  #    Success case prop encoding time   : 0.000
% 0.21/0.52  #    Success case prop solver time     : 0.000
% 0.21/0.52  # Current number of processed clauses  : 516
% 0.21/0.52  #    Positive orientable unit clauses  : 40
% 0.21/0.52  #    Positive unorientable unit clauses: 0
% 0.21/0.52  #    Negative unit clauses             : 2
% 0.21/0.52  #    Non-unit-clauses                  : 474
% 0.21/0.52  # Current number of unprocessed clauses: 3182
% 0.21/0.52  # ...number of literals in the above   : 15020
% 0.21/0.52  # Current number of archived formulas  : 0
% 0.21/0.52  # Current number of archived clauses   : 142
% 0.21/0.52  # Clause-clause subsumption calls (NU) : 53314
% 0.21/0.52  # Rec. Clause-clause subsumption calls : 21145
% 0.21/0.52  # Non-unit clause-clause subsumptions  : 771
% 0.21/0.52  # Unit Clause-clause subsumption calls : 335
% 0.21/0.52  # Rewrite failures with RHS unbound    : 0
% 0.21/0.52  # BW rewrite match attempts            : 48
% 0.21/0.52  # BW rewrite match successes           : 20
% 0.21/0.52  # Condensation attempts                : 0
% 0.21/0.52  # Condensation successes               : 0
% 0.21/0.52  # Termbank termtop insertions          : 146663
% 0.21/0.52  
% 0.21/0.52  # -------------------------------------------------
% 0.21/0.52  # User time                : 0.164 s
% 0.21/0.52  # System time              : 0.010 s
% 0.21/0.52  # Total time               : 0.175 s
% 0.21/0.52  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
