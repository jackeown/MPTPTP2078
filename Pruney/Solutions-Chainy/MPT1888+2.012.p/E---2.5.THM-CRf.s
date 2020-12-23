%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 203 expanded)
%              Number of clauses        :   40 (  73 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  199 (1156 expanded)
%              Number of equality atoms :   22 ( 115 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    7 (   2 average)

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

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(d4_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_tex_2(X1,X2)
              <=> u1_struct_0(X3) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

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

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X20,X21] :
      ( ( ~ v2_struct_0(k1_tex_2(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( v1_pre_topc(k1_tex_2(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) )
      & ( m1_pre_topc(k1_tex_2(X20,X21),X20)
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20)
        | ~ m1_subset_1(X21,u1_struct_0(X20)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v3_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ~ r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))
    & k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_12,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk2_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ( X19 != k1_tex_2(X17,X18)
        | u1_struct_0(X19) = k6_domain_1(u1_struct_0(X17),X18)
        | v2_struct_0(X19)
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) )
      & ( u1_struct_0(X19) != k6_domain_1(u1_struct_0(X17),X18)
        | X19 = k1_tex_2(X17,X18)
        | v2_struct_0(X19)
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | v2_struct_0(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_16]),c_0_14])]),c_0_15])).

fof(c_0_22,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14])])).

cnf(c_0_25,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_21]),c_0_14])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk4_0))),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_14])])).

cnf(c_0_31,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = k6_domain_1(u1_struct_0(X1),X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_12]),c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_28]),c_0_14])])).

fof(c_0_33,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ v3_tdlat_3(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | ~ r2_hidden(X23,k2_pre_topc(X22,k6_domain_1(u1_struct_0(X22),X24)))
      | k2_pre_topc(X22,k6_domain_1(u1_struct_0(X22),X23)) = k2_pre_topc(X22,k6_domain_1(u1_struct_0(X22),X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk4_0)) = k6_domain_1(u1_struct_0(esk2_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) = k6_domain_1(u1_struct_0(esk2_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_16]),c_0_14])]),c_0_15])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_42,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1)) = k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_13]),c_0_39]),c_0_40]),c_0_14])]),c_0_15]),c_0_41])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1)) = k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_16]),c_0_39]),c_0_40]),c_0_14])]),c_0_15]),c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1))) = k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))
    | r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))))) = k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | r1_xboole_0(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))
    | ~ r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),X1)
    | ~ r2_hidden(esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),X1),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_47]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.20/0.41  # and selection function SelectGrCQArEqFirst.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t56_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tex_2)).
% 0.20/0.41  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.20/0.41  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.41  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.41  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 0.20/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.41  fof(t55_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=>k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tex_2)).
% 0.20/0.41  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.41  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t56_tex_2])).
% 0.20/0.41  fof(c_0_9, plain, ![X20, X21]:(((~v2_struct_0(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))&(v1_pre_topc(k1_tex_2(X20,X21))|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20)))))&(m1_pre_topc(k1_tex_2(X20,X21),X20)|(v2_struct_0(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.20/0.41  fof(c_0_10, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v3_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(~r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))&k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.41  fof(c_0_11, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|m1_subset_1(u1_struct_0(X16),k1_zfmisc_1(u1_struct_0(X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.41  cnf(c_0_12, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  fof(c_0_17, plain, ![X13, X14]:(~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.41  cnf(c_0_18, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (m1_pre_topc(k1_tex_2(esk2_0,esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.41  fof(c_0_20, plain, ![X17, X18, X19]:((X19!=k1_tex_2(X17,X18)|u1_struct_0(X19)=k6_domain_1(u1_struct_0(X17),X18)|(v2_struct_0(X19)|~v1_pre_topc(X19)|~m1_pre_topc(X19,X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l1_pre_topc(X17)))&(u1_struct_0(X19)!=k6_domain_1(u1_struct_0(X17),X18)|X19=k1_tex_2(X17,X18)|(v2_struct_0(X19)|~v1_pre_topc(X19)|~m1_pre_topc(X19,X17))|~m1_subset_1(X18,u1_struct_0(X17))|(v2_struct_0(X17)|~l1_pre_topc(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_16]), c_0_14])]), c_0_15])).
% 0.20/0.41  fof(c_0_22, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.41  cnf(c_0_23, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_14])])).
% 0.20/0.41  cnf(c_0_25, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X2),X3)|v2_struct_0(X1)|v2_struct_0(X2)|X1!=k1_tex_2(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.41  cnf(c_0_26, plain, (v1_pre_topc(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_27, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_21]), c_0_14])])).
% 0.20/0.41  cnf(c_0_29, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (m1_subset_1(k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk4_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_14])])).
% 0.20/0.41  cnf(c_0_31, plain, (u1_struct_0(k1_tex_2(X1,X2))=k6_domain_1(u1_struct_0(X1),X2)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]), c_0_12]), c_0_26]), c_0_27])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (m1_subset_1(k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_28]), c_0_14])])).
% 0.20/0.41  fof(c_0_33, plain, ![X22, X23, X24]:(v2_struct_0(X22)|~v2_pre_topc(X22)|~v3_tdlat_3(X22)|~l1_pre_topc(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~m1_subset_1(X24,u1_struct_0(X22))|(~r2_hidden(X23,k2_pre_topc(X22,k6_domain_1(u1_struct_0(X22),X24)))|k2_pre_topc(X22,k6_domain_1(u1_struct_0(X22),X23))=k2_pre_topc(X22,k6_domain_1(u1_struct_0(X22),X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk4_0))=k6_domain_1(u1_struct_0(esk2_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k2_pre_topc(esk2_0,u1_struct_0(k1_tex_2(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_29, c_0_32])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))=k6_domain_1(u1_struct_0(esk2_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_16]), c_0_14])]), c_0_15])).
% 0.20/0.41  cnf(c_0_38, plain, (v2_struct_0(X1)|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.41  fof(c_0_42, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1))=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))|~r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_13]), c_0_39]), c_0_40]), c_0_14])]), c_0_15]), c_0_41])).
% 0.20/0.41  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1))=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|~r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_16]), c_0_39]), c_0_40]), c_0_14])]), c_0_15]), c_0_43])).
% 0.20/0.41  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1)))=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))|r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))))=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|r1_xboole_0(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_51, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (~r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))|~r2_hidden(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),X1)|~r2_hidden(esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),X1),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_47]), c_0_55]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 57
% 0.20/0.41  # Proof object clause steps            : 40
% 0.20/0.41  # Proof object formula steps           : 17
% 0.20/0.41  # Proof object conjectures             : 31
% 0.20/0.41  # Proof object clause conjectures      : 28
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 19
% 0.20/0.41  # Proof object initial formulas used   : 8
% 0.20/0.41  # Proof object generating inferences   : 18
% 0.20/0.41  # Proof object simplifying inferences  : 40
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 8
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 20
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 20
% 0.20/0.41  # Processed clauses                    : 308
% 0.20/0.41  # ...of these trivial                  : 7
% 0.20/0.41  # ...subsumed                          : 54
% 0.20/0.41  # ...remaining for further processing  : 247
% 0.20/0.41  # Other redundant clauses eliminated   : 1
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 2
% 0.20/0.41  # Backward-rewritten                   : 15
% 0.20/0.41  # Generated clauses                    : 478
% 0.20/0.41  # ...of the previous two non-trivial   : 483
% 0.20/0.41  # Contextual simplify-reflections      : 7
% 0.20/0.41  # Paramodulations                      : 475
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 3
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 209
% 0.20/0.41  #    Positive orientable unit clauses  : 42
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 5
% 0.20/0.41  #    Non-unit-clauses                  : 162
% 0.20/0.41  # Current number of unprocessed clauses: 198
% 0.20/0.41  # ...number of literals in the above   : 653
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 37
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4420
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 3407
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 63
% 0.20/0.41  # Unit Clause-clause subsumption calls : 31
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 341
% 0.20/0.41  # BW rewrite match successes           : 2
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 19942
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.054 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.061 s
% 0.20/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
