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
% DateTime   : Thu Dec  3 11:20:49 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 839 expanded)
%              Number of clauses        :   45 ( 321 expanded)
%              Number of leaves         :   10 ( 204 expanded)
%              Depth                    :   18
%              Number of atoms          :  231 (4777 expanded)
%              Number of equality atoms :   14 ( 381 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

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

fof(c_0_11,negated_conjecture,(
    ! [X35] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & v3_tdlat_3(esk4_0)
      & l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & ( ~ m1_subset_1(X35,u1_struct_0(esk4_0))
        | ~ r2_hidden(X35,esk5_0)
        | k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X35))) = k6_domain_1(u1_struct_0(esk4_0),X35) )
      & ~ v2_tex_2(esk5_0,esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_12,plain,(
    ! [X29,X30,X32] :
      ( ( m1_subset_1(esk3_2(X29,X30),u1_struct_0(X29))
        | v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v3_pre_topc(X32,X29)
        | k9_subset_1(u1_struct_0(X29),X30,X32) != k6_domain_1(u1_struct_0(X29),esk3_2(X29,X30))
        | v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

fof(c_0_22,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ( ~ r1_tarski(k1_tarski(X11),X12)
        | r2_hidden(X11,X12) )
      & ( ~ r2_hidden(X11,X12)
        | r1_tarski(k1_tarski(X11),X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ r1_tarski(u1_struct_0(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

fof(c_0_32,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ r2_hidden(esk1_2(u1_struct_0(esk4_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_2(u1_struct_0(esk4_0),X1),u1_struct_0(esk4_0))
    | r2_hidden(esk3_2(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | ~ m1_subset_1(X23,X22)
      | k6_domain_1(X22,X23) = k1_tarski(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_47,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | m1_subset_1(k2_pre_topc(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(esk3_2(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_46]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_51,plain,
    ( v2_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != k6_domain_1(u1_struct_0(X2),esk3_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_18]),c_0_16]),c_0_17])]),c_0_14]),c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_17])])).

fof(c_0_56,plain,(
    ! [X26,X27] :
      ( ( ~ v3_tdlat_3(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | ~ v4_pre_topc(X27,X26)
        | v3_pre_topc(X27,X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( m1_subset_1(esk2_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v4_pre_topc(esk2_1(X26),X26)
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v3_pre_topc(esk2_1(X26),X26)
        | v3_tdlat_3(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_57,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)))) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))
    | ~ v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_60,plain,(
    ! [X24,X25] :
      ( ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | v4_pre_topc(k2_pre_topc(X24,X25),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_61,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)))) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))
    | ~ v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_16]),c_0_17]),c_0_55])])).

cnf(c_0_62,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)))) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_16]),c_0_17]),c_0_53])])).

cnf(c_0_64,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1))) = k6_domain_1(u1_struct_0(esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_50]),c_0_21])]),
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
% 0.12/0.34  % DateTime   : Tue Dec  1 16:11:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.19/0.49  # and selection function PSelectUnlessUniqMaxPos.
% 0.19/0.49  #
% 0.19/0.49  # Preprocessing time       : 0.028 s
% 0.19/0.49  # Presaturation interreduction done
% 0.19/0.49  
% 0.19/0.49  # Proof found!
% 0.19/0.49  # SZS status Theorem
% 0.19/0.49  # SZS output start CNFRefutation
% 0.19/0.49  fof(t58_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 0.19/0.49  fof(t37_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k6_domain_1(u1_struct_0(X1),X3)))))))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 0.19/0.49  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.49  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.49  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.49  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.49  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.49  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.19/0.49  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 0.19/0.49  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 0.19/0.49  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))=>v2_tex_2(X2,X1))))), inference(assume_negation,[status(cth)],[t58_tex_2])).
% 0.19/0.49  fof(c_0_11, negated_conjecture, ![X35]:((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~m1_subset_1(X35,u1_struct_0(esk4_0))|(~r2_hidden(X35,esk5_0)|k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X35)))=k6_domain_1(u1_struct_0(esk4_0),X35)))&~v2_tex_2(esk5_0,esk4_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.19/0.49  fof(c_0_12, plain, ![X29, X30, X32]:((m1_subset_1(esk3_2(X29,X30),u1_struct_0(X29))|v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((r2_hidden(esk3_2(X29,X30),X30)|v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X29)))|(~v3_pre_topc(X32,X29)|k9_subset_1(u1_struct_0(X29),X30,X32)!=k6_domain_1(u1_struct_0(X29),esk3_2(X29,X30)))|v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).
% 0.19/0.49  fof(c_0_13, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.49  cnf(c_0_14, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_15, plain, (r2_hidden(esk3_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_21, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.49  fof(c_0_22, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.49  cnf(c_0_23, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.49  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.49  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_25])).
% 0.19/0.49  cnf(c_0_27, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.49  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.49  fof(c_0_30, plain, ![X11, X12]:((~r1_tarski(k1_tarski(X11),X12)|r2_hidden(X11,X12))&(~r2_hidden(X11,X12)|r1_tarski(k1_tarski(X11),X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.49  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~r1_tarski(u1_struct_0(esk4_0),X1)), inference(spm,[status(thm)],[c_0_26, c_0_18])).
% 0.19/0.49  fof(c_0_32, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.49  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(esk1_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.49  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.19/0.49  cnf(c_0_35, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.49  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~r2_hidden(esk1_2(u1_struct_0(esk4_0),X1),X1)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 0.19/0.49  cnf(c_0_37, negated_conjecture, (r2_hidden(esk1_2(u1_struct_0(esk4_0),X1),u1_struct_0(esk4_0))|r2_hidden(esk3_2(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.19/0.49  cnf(c_0_38, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.49  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.49  cnf(c_0_40, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_35])).
% 0.19/0.49  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.49  fof(c_0_42, plain, ![X22, X23]:(v1_xboole_0(X22)|~m1_subset_1(X23,X22)|k6_domain_1(X22,X23)=k1_tarski(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.49  cnf(c_0_43, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.49  cnf(c_0_44, negated_conjecture, (m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.49  cnf(c_0_45, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.49  cnf(c_0_46, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  fof(c_0_47, plain, ![X20, X21]:(~l1_pre_topc(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|m1_subset_1(k2_pre_topc(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.19/0.49  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_41])).
% 0.19/0.49  cnf(c_0_49, negated_conjecture, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(esk3_2(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.49  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_46]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.49  cnf(c_0_51, plain, (v2_tex_2(X3,X2)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=k6_domain_1(u1_struct_0(X2),esk3_2(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.49  cnf(c_0_52, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.49  cnf(c_0_53, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.19/0.49  cnf(c_0_54, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1)!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_18]), c_0_16]), c_0_17])]), c_0_14]), c_0_19])).
% 0.19/0.49  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_17])])).
% 0.19/0.49  fof(c_0_56, plain, ![X26, X27]:((~v3_tdlat_3(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~v4_pre_topc(X27,X26)|v3_pre_topc(X27,X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((m1_subset_1(esk2_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&((v4_pre_topc(esk2_1(X26),X26)|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~v3_pre_topc(esk2_1(X26),X26)|v3_tdlat_3(X26)|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 0.19/0.49  cnf(c_0_57, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))))!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))|~v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.49  cnf(c_0_58, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.49  cnf(c_0_59, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  fof(c_0_60, plain, ![X24, X25]:(~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|v4_pre_topc(k2_pre_topc(X24,X25),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 0.19/0.49  cnf(c_0_61, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))))!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))|~v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_16]), c_0_17]), c_0_55])])).
% 0.19/0.49  cnf(c_0_62, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.49  cnf(c_0_63, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))))!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_16]), c_0_17]), c_0_53])])).
% 0.19/0.49  cnf(c_0_64, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1)))=k6_domain_1(u1_struct_0(esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.49  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_50]), c_0_21])]), ['proof']).
% 0.19/0.49  # SZS output end CNFRefutation
% 0.19/0.49  # Proof object total steps             : 66
% 0.19/0.49  # Proof object clause steps            : 45
% 0.19/0.49  # Proof object formula steps           : 21
% 0.19/0.49  # Proof object conjectures             : 29
% 0.19/0.49  # Proof object clause conjectures      : 26
% 0.19/0.49  # Proof object formula conjectures     : 3
% 0.19/0.49  # Proof object initial clauses used    : 21
% 0.19/0.49  # Proof object initial formulas used   : 10
% 0.19/0.49  # Proof object generating inferences   : 24
% 0.19/0.49  # Proof object simplifying inferences  : 31
% 0.19/0.49  # Training examples: 0 positive, 0 negative
% 0.19/0.49  # Parsed axioms                        : 11
% 0.19/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.49  # Initial clauses                      : 26
% 0.19/0.49  # Removed in clause preprocessing      : 0
% 0.19/0.49  # Initial clauses in saturation        : 26
% 0.19/0.49  # Processed clauses                    : 1005
% 0.19/0.49  # ...of these trivial                  : 11
% 0.19/0.49  # ...subsumed                          : 441
% 0.19/0.49  # ...remaining for further processing  : 553
% 0.19/0.49  # Other redundant clauses eliminated   : 0
% 0.19/0.49  # Clauses deleted for lack of memory   : 0
% 0.19/0.49  # Backward-subsumed                    : 75
% 0.19/0.49  # Backward-rewritten                   : 0
% 0.19/0.49  # Generated clauses                    : 3563
% 0.19/0.49  # ...of the previous two non-trivial   : 3451
% 0.19/0.49  # Contextual simplify-reflections      : 1
% 0.19/0.49  # Paramodulations                      : 3563
% 0.19/0.49  # Factorizations                       : 0
% 0.19/0.49  # Equation resolutions                 : 0
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
% 0.19/0.49  # Current number of processed clauses  : 452
% 0.19/0.49  #    Positive orientable unit clauses  : 66
% 0.19/0.49  #    Positive unorientable unit clauses: 0
% 0.19/0.49  #    Negative unit clauses             : 24
% 0.19/0.49  #    Non-unit-clauses                  : 362
% 0.19/0.49  # Current number of unprocessed clauses: 2491
% 0.19/0.49  # ...number of literals in the above   : 9487
% 0.19/0.49  # Current number of archived formulas  : 0
% 0.19/0.49  # Current number of archived clauses   : 101
% 0.19/0.49  # Clause-clause subsumption calls (NU) : 16465
% 0.19/0.49  # Rec. Clause-clause subsumption calls : 9092
% 0.19/0.49  # Non-unit clause-clause subsumptions  : 341
% 0.19/0.49  # Unit Clause-clause subsumption calls : 638
% 0.19/0.49  # Rewrite failures with RHS unbound    : 0
% 0.19/0.49  # BW rewrite match attempts            : 854
% 0.19/0.49  # BW rewrite match successes           : 0
% 0.19/0.49  # Condensation attempts                : 0
% 0.19/0.49  # Condensation successes               : 0
% 0.19/0.49  # Termbank termtop insertions          : 126984
% 0.19/0.49  
% 0.19/0.49  # -------------------------------------------------
% 0.19/0.49  # User time                : 0.135 s
% 0.19/0.49  # System time              : 0.009 s
% 0.19/0.49  # Total time               : 0.145 s
% 0.19/0.49  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
