%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 653 expanded)
%              Number of clauses        :   59 ( 252 expanded)
%              Number of leaves         :   13 ( 160 expanded)
%              Depth                    :   14
%              Number of atoms          :  265 (2995 expanded)
%              Number of equality atoms :   36 ( 332 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(t40_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_xboole_0(X2,X3)
                  & v3_pre_topc(X2,X1) )
               => r1_xboole_0(X2,k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t55_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
               => k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
                  | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_tex_2])).

fof(c_0_14,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v3_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ~ r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    & k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) != k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_xboole_0(u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | esk2_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | k6_domain_1(X24,X25) = k1_tarski(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(k2_pre_topc(X18,X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_33,plain,(
    ! [X26,X27] :
      ( ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | v4_pre_topc(k2_pre_topc(X26,X27),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_34,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_37,plain,(
    ! [X31,X32,X33] :
      ( ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
      | ~ r1_xboole_0(X32,X33)
      | ~ v3_pre_topc(X32,X31)
      | r1_xboole_0(X32,k2_pre_topc(X31,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).

fof(c_0_38,plain,(
    ! [X28,X29] :
      ( ( ~ v3_tdlat_3(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v4_pre_topc(X29,X28)
        | v3_pre_topc(X29,X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk3_1(X28),k1_zfmisc_1(u1_struct_0(X28)))
        | v3_tdlat_3(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v4_pre_topc(esk3_1(X28),X28)
        | v3_tdlat_3(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v3_pre_topc(esk3_1(X28),X28)
        | v3_tdlat_3(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_41,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k2_tarski(esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_32])).

fof(c_0_45,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( k2_tarski(esk5_0,esk5_0) = k6_domain_1(u1_struct_0(esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X2,k2_pre_topc(X1,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_40]),c_0_42]),c_0_18])])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_36]),c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_46])).

fof(c_0_56,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ v3_tdlat_3(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | ~ r2_hidden(X35,k2_pre_topc(X34,k6_domain_1(u1_struct_0(X34),X36)))
      | k2_pre_topc(X34,k6_domain_1(u1_struct_0(X34),X35)) = k2_pre_topc(X34,k6_domain_1(u1_struct_0(X34),X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_40]),c_0_42]),c_0_18])])).

cnf(c_0_58,negated_conjecture,
    ( v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_42]),c_0_18])])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_60,negated_conjecture,
    ( esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = esk6_0
    | r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r1_xboole_0(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_54]),c_0_42]),c_0_18])])).

cnf(c_0_62,negated_conjecture,
    ( esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_53])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | ~ r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_49]),c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_0,X1)
    | r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_49]),c_0_58])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk5_0,X1)
    | r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1)) = k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_31]),c_0_50]),c_0_42]),c_0_18])]),c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) != k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_54]),c_0_18])])).

cnf(c_0_71,negated_conjecture,
    ( v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_54]),c_0_42]),c_0_18])])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_36]),c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_70]),c_0_50]),c_0_71]),c_0_42]),c_0_18])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(sr,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_70]),c_0_76])]),c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | r1_xboole_0(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_53])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_65])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.19/0.49  # and selection function SelectGrCQArEqFirst.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.032 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(t56_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 0.19/0.49  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.49  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.49  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.49  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.49  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.19/0.49  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.49  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.19/0.49  fof(t40_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_xboole_0(X2,X3)&v3_pre_topc(X2,X1))=>r1_xboole_0(X2,k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_tsep_1)).
% 0.19/0.49  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.19/0.49  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.49  fof(t55_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=>k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 0.19/0.49  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t56_tex_2])).
% 0.19/0.49  fof(c_0_14, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.49  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(~r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))&k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))!=k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.19/0.49  fof(c_0_16, plain, ![X21]:(v2_struct_0(X21)|~l1_struct_0(X21)|~v1_xboole_0(u1_struct_0(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.49  cnf(c_0_17, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.49  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  fof(c_0_19, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|X12=X10|X11!=k1_tarski(X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k1_tarski(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|esk2_2(X14,X15)!=X14|X15=k1_tarski(X14))&(r2_hidden(esk2_2(X14,X15),X15)|esk2_2(X14,X15)=X14|X15=k1_tarski(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.49  fof(c_0_20, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.49  fof(c_0_21, plain, ![X24, X25]:(v1_xboole_0(X24)|~m1_subset_1(X25,X24)|k6_domain_1(X24,X25)=k1_tarski(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.49  fof(c_0_22, plain, ![X22, X23]:(v1_xboole_0(X22)|~m1_subset_1(X23,X22)|m1_subset_1(k6_domain_1(X22,X23),k1_zfmisc_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.19/0.49  cnf(c_0_23, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.49  cnf(c_0_24, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.49  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_26, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.49  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.49  cnf(c_0_28, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.49  fof(c_0_29, plain, ![X18, X19]:(~l1_pre_topc(X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(k2_pre_topc(X18,X19),k1_zfmisc_1(u1_struct_0(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.49  cnf(c_0_30, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.19/0.49  fof(c_0_33, plain, ![X26, X27]:(~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|v4_pre_topc(k2_pre_topc(X26,X27),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.19/0.49  cnf(c_0_34, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.49  cnf(c_0_35, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_28, c_0_27])).
% 0.19/0.49  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  fof(c_0_37, plain, ![X31, X32, X33]:(~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|(~r1_xboole_0(X32,X33)|~v3_pre_topc(X32,X31)|r1_xboole_0(X32,k2_pre_topc(X31,X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_tsep_1])])])).
% 0.19/0.49  fof(c_0_38, plain, ![X28, X29]:((~v3_tdlat_3(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(~v4_pre_topc(X29,X28)|v3_pre_topc(X29,X28)))|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&((m1_subset_1(esk3_1(X28),k1_zfmisc_1(u1_struct_0(X28)))|v3_tdlat_3(X28)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&((v4_pre_topc(esk3_1(X28),X28)|v3_tdlat_3(X28)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(~v3_pre_topc(esk3_1(X28),X28)|v3_tdlat_3(X28)|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.19/0.49  cnf(c_0_39, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.49  cnf(c_0_40, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.19/0.49  cnf(c_0_41, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.49  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_43, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.49  cnf(c_0_44, negated_conjecture, (k2_tarski(esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk4_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_32])).
% 0.19/0.49  fof(c_0_45, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.49  cnf(c_0_46, negated_conjecture, (k2_tarski(esk5_0,esk5_0)=k6_domain_1(u1_struct_0(esk4_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32])).
% 0.19/0.49  cnf(c_0_47, plain, (r1_xboole_0(X2,k2_pre_topc(X1,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_xboole_0(X2,X3)|~v3_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.49  cnf(c_0_48, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.49  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18])])).
% 0.19/0.49  cnf(c_0_50, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_51, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_40]), c_0_42]), c_0_18])])).
% 0.19/0.49  cnf(c_0_52, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.49  cnf(c_0_53, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.49  cnf(c_0_54, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_36]), c_0_32])).
% 0.19/0.49  cnf(c_0_55, negated_conjecture, (X1=esk5_0|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_43, c_0_46])).
% 0.19/0.49  fof(c_0_56, plain, ![X34, X35, X36]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~v3_tdlat_3(X34)|~l1_pre_topc(X34)|(~m1_subset_1(X35,u1_struct_0(X34))|(~m1_subset_1(X36,u1_struct_0(X34))|(~r2_hidden(X35,k2_pre_topc(X34,k6_domain_1(u1_struct_0(X34),X36)))|k2_pre_topc(X34,k6_domain_1(u1_struct_0(X34),X35))=k2_pre_topc(X34,k6_domain_1(u1_struct_0(X34),X36)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).
% 0.19/0.49  cnf(c_0_57, negated_conjecture, (r1_xboole_0(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_40]), c_0_42]), c_0_18])])).
% 0.19/0.49  cnf(c_0_58, negated_conjecture, (v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_42]), c_0_18])])).
% 0.19/0.49  cnf(c_0_59, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.49  cnf(c_0_60, negated_conjecture, (esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))=esk6_0|r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.49  cnf(c_0_61, negated_conjecture, (r1_xboole_0(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_54]), c_0_42]), c_0_18])])).
% 0.19/0.49  cnf(c_0_62, negated_conjecture, (esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_53])).
% 0.19/0.49  cnf(c_0_63, plain, (v2_struct_0(X1)|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.49  cnf(c_0_64, negated_conjecture, (r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|~r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_49]), c_0_58])])).
% 0.19/0.49  cnf(c_0_65, negated_conjecture, (r2_hidden(esk6_0,X1)|r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.49  cnf(c_0_66, negated_conjecture, (r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_49]), c_0_58])])).
% 0.19/0.49  cnf(c_0_67, negated_conjecture, (r2_hidden(esk5_0,X1)|r1_xboole_0(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_59, c_0_62])).
% 0.19/0.49  cnf(c_0_68, negated_conjecture, (k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1))=k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_31]), c_0_50]), c_0_42]), c_0_18])]), c_0_25])).
% 0.19/0.49  cnf(c_0_69, negated_conjecture, (k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))!=k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_70, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_54]), c_0_18])])).
% 0.19/0.49  cnf(c_0_71, negated_conjecture, (v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_54]), c_0_42]), c_0_18])])).
% 0.19/0.49  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.49  cnf(c_0_73, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.49  cnf(c_0_74, negated_conjecture, (r2_hidden(esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.49  cnf(c_0_75, negated_conjecture, (~r2_hidden(esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_36]), c_0_69])).
% 0.19/0.49  cnf(c_0_76, negated_conjecture, (v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_70]), c_0_50]), c_0_71]), c_0_42]), c_0_18])])).
% 0.19/0.49  cnf(c_0_77, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.49  cnf(c_0_78, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|~r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.49  cnf(c_0_79, negated_conjecture, (r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(sr,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.49  cnf(c_0_80, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_70]), c_0_76])]), c_0_77])).
% 0.19/0.49  cnf(c_0_81, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|r1_xboole_0(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_78, c_0_53])).
% 0.19/0.49  cnf(c_0_82, negated_conjecture, (~r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~r2_hidden(X1,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_72, c_0_79])).
% 0.19/0.49  cnf(c_0_83, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_80, c_0_65])).
% 0.19/0.49  cnf(c_0_84, negated_conjecture, (r2_hidden(esk6_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_77, c_0_81])).
% 0.19/0.49  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 86
% 0.19/0.49  # Proof object clause steps            : 59
% 0.19/0.49  # Proof object formula steps           : 27
% 0.19/0.49  # Proof object conjectures             : 45
% 0.19/0.49  # Proof object clause conjectures      : 42
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 22
% 0.19/0.49  # Proof object initial formulas used   : 13
% 0.19/0.49  # Proof object generating inferences   : 33
% 0.19/0.49  # Proof object simplifying inferences  : 50
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 13
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 28
% 0.19/0.49  # Removed in clause preprocessing      : 1
% 0.19/0.49  # Initial clauses in saturation        : 27
% 0.19/0.49  # Processed clauses                    : 456
% 0.19/0.49  # ...of these trivial                  : 1
% 0.19/0.49  # ...subsumed                          : 137
% 0.19/0.49  # ...remaining for further processing  : 318
% 0.19/0.49  # Other redundant clauses eliminated   : 16
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 5
% 0.19/0.49  # Backward-rewritten                   : 7
% 0.19/0.49  # Generated clauses                    : 3097
% 0.19/0.49  # ...of the previous two non-trivial   : 2991
% 0.19/0.49  # Contextual simplify-reflections      : 0
% 0.19/0.49  # Paramodulations                      : 3072
% 0.19/0.49  # Factorizations                       : 8
% 0.19/0.49  # Equation resolutions                 : 16
% 0.19/0.49  # Propositional unsat checks           : 0
% 0.19/0.49  #    Propositional check models        : 0
% 0.19/0.49  #    Propositional check unsatisfiable : 0
% 0.19/0.49  #    Propositional clauses             : 0
% 0.19/0.49  #    Propositional clauses after purity: 0
% 0.19/0.49  #    Propositional unsat core size     : 0
% 0.19/0.49  #    Propositional preprocessing time  : 0.000
% 0.19/0.49  #    Propositional encoding time       : 0.000
% 0.19/0.49  #    Propositional solver time         : 0.000
% 0.19/0.49  #    Success case prop preproc time    : 0.000
% 0.19/0.49  #    Success case prop encoding time   : 0.000
% 0.19/0.49  #    Success case prop solver time     : 0.000
% 0.19/0.49  # Current number of processed clauses  : 275
% 0.19/0.49  #    Positive orientable unit clauses  : 68
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 6
% 0.19/0.49  #    Non-unit-clauses                  : 201
% 0.19/0.49  # Current number of unprocessed clauses: 2585
% 0.19/0.49  # ...number of literals in the above   : 13409
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 42
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 5251
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 3914
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 141
% 0.19/0.49  # Unit Clause-clause subsumption calls : 145
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 316
% 0.19/0.49  # BW rewrite match successes           : 3
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 64043
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.147 s
% 0.19/0.49  # System time              : 0.007 s
% 0.19/0.49  # Total time               : 0.154 s
% 0.19/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
