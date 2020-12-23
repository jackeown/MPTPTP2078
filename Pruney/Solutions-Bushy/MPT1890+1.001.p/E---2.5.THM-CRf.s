%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1890+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:00 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 150 expanded)
%              Number of clauses        :   25 (  48 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  181 (1047 expanded)
%              Number of equality atoms :   10 (  97 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   23 (   4 average)
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

fof(t57_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v4_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k6_domain_1(u1_struct_0(X1),X3) ) ) ) )
           => v2_tex_2(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tex_2)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X14,X15,X17] :
      ( ( m1_subset_1(esk1_2(X14,X15),u1_struct_0(X14))
        | v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ v3_tdlat_3(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ v3_tdlat_3(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v4_pre_topc(X17,X14)
        | k9_subset_1(u1_struct_0(X14),X15,X17) != k6_domain_1(u1_struct_0(X14),esk1_2(X14,X15))
        | v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ v3_tdlat_3(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_tex_2])])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X23] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & v3_tdlat_3(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( ~ m1_subset_1(X23,u1_struct_0(esk2_0))
        | ~ r2_hidden(X23,esk3_0)
        | k9_subset_1(u1_struct_0(esk2_0),esk3_0,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X23))) = k6_domain_1(u1_struct_0(esk2_0),X23) )
      & ~ v2_tex_2(esk3_0,esk2_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_10,plain,
    ( v2_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != k6_domain_1(u1_struct_0(X2),esk1_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v3_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),esk3_0,k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1))) = k6_domain_1(u1_struct_0(esk2_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v3_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_tex_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | v4_pre_topc(k2_pre_topc(X9,X10),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_19,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),X1) != k6_domain_1(u1_struct_0(esk2_0),esk1_2(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0)
    | ~ v4_pre_topc(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1)),esk2_0)
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_20,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X5,X6] :
      ( ~ l1_pre_topc(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | m1_subset_1(k2_pre_topc(X5,X6),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_22,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),X1) != k6_domain_1(u1_struct_0(esk2_0),esk1_2(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(k2_pre_topc(esk2_0,k6_domain_1(u1_struct_0(esk2_0),X1)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_13]),c_0_15])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),X1) != k6_domain_1(u1_struct_0(esk2_0),esk1_2(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( v1_xboole_0(X7)
      | ~ m1_subset_1(X8,X7)
      | m1_subset_1(k6_domain_1(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_26,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk1_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(esk1_2(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_31,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0)
    | ~ m1_subset_1(esk1_2(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | m1_subset_1(esk1_2(X2,X1),X3)
    | ~ v3_tdlat_3(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(esk1_2(esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_36,plain,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v3_tdlat_3(X2)
    | ~ v2_pre_topc(X2)
    | ~ v1_xboole_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_16]),c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( v2_tex_2(X1,X2)
    | v2_struct_0(X2)
    | ~ v3_tdlat_3(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_38]),c_0_12]),c_0_13]),c_0_14]),c_0_15])]),c_0_17]),
    [proof]).

%------------------------------------------------------------------------------
