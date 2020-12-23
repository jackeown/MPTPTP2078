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
% DateTime   : Thu Dec  3 11:20:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 141 expanded)
%              Number of clauses        :   34 (  53 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  172 ( 731 expanded)
%              Number of equality atoms :   11 (  65 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_8,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_10,negated_conjecture,(
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

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_14,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X17)
      | ~ m1_subset_1(X18,X17)
      | m1_subset_1(k6_domain_1(X17,X18),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v3_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ~ r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))
    & k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ v3_tdlat_3(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | ~ r2_hidden(X20,k2_pre_topc(X19,k6_domain_1(u1_struct_0(X19),X21)))
      | k2_pre_topc(X19,k6_domain_1(u1_struct_0(X19),X20)) = k2_pre_topc(X19,k6_domain_1(u1_struct_0(X19),X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_2(X1,k2_pre_topc(X2,X3)),u1_struct_0(X2))
    | r1_xboole_0(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk1_2(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))
    | r1_xboole_0(k2_pre_topc(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),esk1_2(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))))) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))
    | v2_struct_0(X1)
    | r1_xboole_0(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(esk1_2(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))),u1_struct_0(esk2_0))
    | r1_xboole_0(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),esk1_2(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),X3))) = k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))
    | v2_struct_0(X1)
    | r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),X3)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),X3),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1),u1_struct_0(esk2_0))
    | r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_26])])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))))) = k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | r1_xboole_0(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_26]),c_0_20])]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1))) = k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32]),c_0_33]),c_0_26]),c_0_22])]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) != k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_41,plain,(
    ! [X16] :
      ( v2_struct_0(X16)
      | ~ l1_struct_0(X16)
      | ~ v1_xboole_0(u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

fof(c_0_47,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_48,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_34])).

cnf(c_0_49,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n018.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.38  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.38  fof(t56_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_tex_2)).
% 0.20/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.20/0.38  fof(t55_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=>k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tex_2)).
% 0.20/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.38  fof(c_0_8, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.38  fof(c_0_9, plain, ![X13, X14]:(~l1_pre_topc(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|m1_subset_1(k2_pre_topc(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t56_tex_2])).
% 0.20/0.38  cnf(c_0_11, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_13, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X17, X18]:(v1_xboole_0(X17)|~m1_subset_1(X18,X17)|m1_subset_1(k6_domain_1(X17,X18),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.20/0.38  fof(c_0_15, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v3_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(~r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))&k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.20/0.38  fof(c_0_16, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~v3_tdlat_3(X19)|~l1_pre_topc(X19)|(~m1_subset_1(X20,u1_struct_0(X19))|(~m1_subset_1(X21,u1_struct_0(X19))|(~r2_hidden(X20,k2_pre_topc(X19,k6_domain_1(u1_struct_0(X19),X21)))|k2_pre_topc(X19,k6_domain_1(u1_struct_0(X19),X20))=k2_pre_topc(X19,k6_domain_1(u1_struct_0(X19),X21)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_tex_2])])])])).
% 0.20/0.38  cnf(c_0_17, plain, (m1_subset_1(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,k2_pre_topc(X2,X3))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_19, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_23, plain, (v2_struct_0(X1)|k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_24, plain, (m1_subset_1(esk1_2(X1,k2_pre_topc(X2,X3)),u1_struct_0(X2))|r1_xboole_0(X1,k2_pre_topc(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_27, plain, (m1_subset_1(esk1_2(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))|r1_xboole_0(k2_pre_topc(X1,X2),X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.20/0.38  cnf(c_0_29, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_30, plain, (k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),esk1_2(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))|v2_struct_0(X1)|r1_xboole_0(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(esk1_2(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))),u1_struct_0(esk2_0))|r1_xboole_0(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (v3_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_35, plain, (k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),esk1_2(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),X3)))=k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2))|v2_struct_0(X1)|r1_xboole_0(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),X3)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X2)),X3),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1),u1_struct_0(esk2_0))|r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_26])])).
% 0.20/0.38  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))))=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|r1_xboole_0(X1,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_26]), c_0_20])]), c_0_34])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk1_2(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1)))=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))|v1_xboole_0(u1_struct_0(esk2_0))|r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32]), c_0_33]), c_0_26]), c_0_22])]), c_0_34])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))!=k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  fof(c_0_41, plain, ![X16]:(v2_struct_0(X16)|~l1_struct_0(X16)|~v1_xboole_0(u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.38  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_18])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (~r1_xboole_0(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_45, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.20/0.38  fof(c_0_47, plain, ![X15]:(~l1_pre_topc(X15)|l1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_34])).
% 0.20/0.38  cnf(c_0_49, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_26])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 51
% 0.20/0.38  # Proof object clause steps            : 34
% 0.20/0.38  # Proof object formula steps           : 17
% 0.20/0.38  # Proof object conjectures             : 21
% 0.20/0.38  # Proof object clause conjectures      : 18
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 17
% 0.20/0.38  # Proof object initial formulas used   : 8
% 0.20/0.38  # Proof object generating inferences   : 17
% 0.20/0.38  # Proof object simplifying inferences  : 21
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 8
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 17
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 17
% 0.20/0.38  # Processed clauses                    : 107
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 8
% 0.20/0.38  # ...remaining for further processing  : 99
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 49
% 0.20/0.38  # Generated clauses                    : 161
% 0.20/0.38  # ...of the previous two non-trivial   : 159
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 161
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 33
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 23
% 0.20/0.38  # Current number of unprocessed clauses: 86
% 0.20/0.38  # ...number of literals in the above   : 356
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 66
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1646
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 454
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.20/0.38  # Unit Clause-clause subsumption calls : 2
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 7541
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.007 s
% 0.20/0.38  # Total time               : 0.041 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
