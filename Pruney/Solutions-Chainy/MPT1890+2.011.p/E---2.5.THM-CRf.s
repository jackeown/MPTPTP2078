%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:49 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 169 expanded)
%              Number of clauses        :   31 (  59 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  201 (1044 expanded)
%              Number of equality atoms :   13 ( 100 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,X2)
                 => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t37_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(t24_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v3_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => v3_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( r2_hidden(X3,X2)
                   => k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3))) = k6_domain_1(u1_struct_0(X1),X3) ) )
             => v2_tex_2(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_tex_2])).

fof(c_0_11,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | m1_subset_1(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,negated_conjecture,(
    ! [X28] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & v3_tdlat_3(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( ~ m1_subset_1(X28,u1_struct_0(esk3_0))
        | ~ r2_hidden(X28,esk4_0)
        | k9_subset_1(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X28))) = k6_domain_1(u1_struct_0(esk3_0),X28) )
      & ~ v2_tex_2(esk4_0,esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X22,X23,X25] :
      ( ( m1_subset_1(esk2_2(X22,X23),u1_struct_0(X22))
        | v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v3_pre_topc(X25,X22)
        | k9_subset_1(u1_struct_0(X22),X23,X25) != k6_domain_1(u1_struct_0(X22),esk2_2(X22,X23))
        | v2_tex_2(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( v2_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != k6_domain_1(u1_struct_0(X2),esk2_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1))) = k6_domain_1(u1_struct_0(esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1))) = k6_domain_1(u1_struct_0(esk3_0),X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_25,plain,(
    ! [X19,X20] :
      ( ( ~ v3_tdlat_3(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v4_pre_topc(X20,X19)
        | v3_pre_topc(X20,X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk1_1(X19),k1_zfmisc_1(u1_struct_0(X19)))
        | v3_tdlat_3(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v4_pre_topc(esk1_1(X19),X19)
        | v3_tdlat_3(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ v3_pre_topc(esk1_1(X19),X19)
        | v3_tdlat_3(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

fof(c_0_26,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(X5))
      | m1_subset_1(k9_subset_1(X5,X6,X7),k1_zfmisc_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_27,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ v3_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | v4_pre_topc(k2_pre_topc(X17,X18),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ v4_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_17]),c_0_18])])).

cnf(c_0_34,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

fof(c_0_36,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
      | m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

fof(c_0_37,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | m1_subset_1(k6_domain_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_2(esk3_0,esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_15]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_17]),c_0_18])]),c_0_35])).

cnf(c_0_40,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_2(esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_38])).

fof(c_0_43,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_44,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),X1) != k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18])])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_38])])).

fof(c_0_48,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_49,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_20])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.031 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t58_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 0.12/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.12/0.38  fof(t37_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k6_domain_1(u1_struct_0(X1),X3)))))))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 0.12/0.38  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.12/0.38  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.12/0.38  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.12/0.38  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.12/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.12/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.12/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))=>v2_tex_2(X2,X1))))), inference(assume_negation,[status(cth)],[t58_tex_2])).
% 0.12/0.38  fof(c_0_11, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|m1_subset_1(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.12/0.38  fof(c_0_12, negated_conjecture, ![X28]:((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v3_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&((~m1_subset_1(X28,u1_struct_0(esk3_0))|(~r2_hidden(X28,esk4_0)|k9_subset_1(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X28)))=k6_domain_1(u1_struct_0(esk3_0),X28)))&~v2_tex_2(esk4_0,esk3_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.12/0.38  fof(c_0_13, plain, ![X22, X23, X25]:((m1_subset_1(esk2_2(X22,X23),u1_struct_0(X22))|v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&((r2_hidden(esk2_2(X22,X23),X23)|v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))|(~v3_pre_topc(X25,X22)|k9_subset_1(u1_struct_0(X22),X23,X25)!=k6_domain_1(u1_struct_0(X22),esk2_2(X22,X23)))|v2_tex_2(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).
% 0.12/0.38  cnf(c_0_14, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_16, plain, (v2_tex_2(X3,X2)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=k6_domain_1(u1_struct_0(X2),esk2_2(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)))=k6_domain_1(u1_struct_0(esk3_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1)!=k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_15]), c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk4_0,k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)))=k6_domain_1(u1_struct_0(esk3_0),X1)|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.38  fof(c_0_25, plain, ![X19, X20]:((~v3_tdlat_3(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|(~v4_pre_topc(X20,X19)|v3_pre_topc(X20,X19)))|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_subset_1(esk1_1(X19),k1_zfmisc_1(u1_struct_0(X19)))|v3_tdlat_3(X19)|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((v4_pre_topc(esk1_1(X19),X19)|v3_tdlat_3(X19)|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~v3_pre_topc(esk1_1(X19),X19)|v3_tdlat_3(X19)|(~v2_pre_topc(X19)|~l1_pre_topc(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.12/0.38  fof(c_0_26, plain, ![X5, X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(X5))|m1_subset_1(k9_subset_1(X5,X6,X7),k1_zfmisc_1(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),X1)!=k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))|~v3_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.38  cnf(c_0_28, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.38  fof(c_0_30, plain, ![X17, X18]:(~v2_pre_topc(X17)|~l1_pre_topc(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|v4_pre_topc(k2_pre_topc(X17,X18),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.12/0.38  cnf(c_0_31, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_32, plain, (r2_hidden(esk2_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),X1)!=k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))|~v4_pre_topc(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),esk3_0)|~r2_hidden(X1,esk4_0)|~m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_17]), c_0_18])])).
% 0.12/0.38  cnf(c_0_34, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)|~m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.12/0.38  fof(c_0_36, plain, ![X11, X12]:(~l1_pre_topc(X11)|~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))|m1_subset_1(k2_pre_topc(X11,X12),k1_zfmisc_1(u1_struct_0(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.12/0.38  fof(c_0_37, plain, ![X15, X16]:(v1_xboole_0(X15)|~m1_subset_1(X16,X15)|m1_subset_1(k6_domain_1(X15,X16),k1_zfmisc_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.12/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk2_2(esk3_0,esk4_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_15]), c_0_17]), c_0_18])]), c_0_19]), c_0_20])).
% 0.12/0.38  cnf(c_0_39, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),X1)!=k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)|~m1_subset_1(k2_pre_topc(esk3_0,k6_domain_1(u1_struct_0(esk3_0),X1)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_17]), c_0_18])]), c_0_35])).
% 0.12/0.38  cnf(c_0_40, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_41, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk2_2(esk3_0,esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_22, c_0_38])).
% 0.12/0.38  fof(c_0_43, plain, ![X14]:(v2_struct_0(X14)|~l1_struct_0(X14)|~v1_xboole_0(u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.12/0.38  cnf(c_0_44, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),X1)!=k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0))|~r2_hidden(X1,esk4_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18])])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk2_2(esk3_0,esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.38  cnf(c_0_46, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_38])])).
% 0.12/0.38  fof(c_0_48, plain, ![X13]:(~l1_pre_topc(X13)|l1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_20])).
% 0.12/0.38  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_51, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_18])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 52
% 0.12/0.38  # Proof object clause steps            : 31
% 0.12/0.38  # Proof object formula steps           : 21
% 0.12/0.38  # Proof object conjectures             : 24
% 0.12/0.38  # Proof object clause conjectures      : 21
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 17
% 0.12/0.38  # Proof object initial formulas used   : 10
% 0.12/0.38  # Proof object generating inferences   : 13
% 0.12/0.38  # Proof object simplifying inferences  : 26
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 10
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 21
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 21
% 0.12/0.38  # Processed clauses                    : 63
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 0
% 0.12/0.38  # ...remaining for further processing  : 63
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 2
% 0.12/0.38  # Backward-rewritten                   : 3
% 0.12/0.38  # Generated clauses                    : 46
% 0.12/0.38  # ...of the previous two non-trivial   : 40
% 0.12/0.38  # Contextual simplify-reflections      : 2
% 0.12/0.38  # Paramodulations                      : 46
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 37
% 0.12/0.38  #    Positive orientable unit clauses  : 7
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 27
% 0.12/0.38  # Current number of unprocessed clauses: 19
% 0.12/0.38  # ...number of literals in the above   : 86
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 26
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 328
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 105
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.38  # Unit Clause-clause subsumption calls : 34
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 1
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 3612
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.033 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.039 s
% 0.12/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
