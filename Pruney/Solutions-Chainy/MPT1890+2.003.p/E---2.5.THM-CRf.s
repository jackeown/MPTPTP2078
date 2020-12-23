%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:48 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 577 expanded)
%              Number of clauses        :   49 ( 226 expanded)
%              Number of leaves         :   12 ( 139 expanded)
%              Depth                    :   17
%              Number of atoms          :  254 (3165 expanded)
%              Number of equality atoms :   22 ( 328 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

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

fof(fc1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k2_pre_topc(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,negated_conjecture,(
    ! [X44] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & v3_tdlat_3(esk4_0)
      & l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & ( ~ m1_subset_1(X44,u1_struct_0(esk4_0))
        | ~ r2_hidden(X44,esk5_0)
        | k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X44))) = k6_domain_1(u1_struct_0(esk4_0),X44) )
      & ~ v2_tex_2(esk5_0,esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_14,plain,(
    ! [X38,X39,X41] :
      ( ( m1_subset_1(esk3_2(X38,X39),u1_struct_0(X38))
        | v2_tex_2(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(esk3_2(X38,X39),X39)
        | v2_tex_2(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ v3_pre_topc(X41,X38)
        | k9_subset_1(u1_struct_0(X38),X39,X41) != k6_domain_1(u1_struct_0(X38),esk3_2(X38,X39))
        | v2_tex_2(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | ~ v1_xboole_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_30,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(k1_tarski(X19),k1_zfmisc_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk5_0),X1)
    | ~ r1_tarski(esk5_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_31])).

cnf(c_0_36,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(X1))
    | ~ r1_tarski(esk5_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_44,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | m1_subset_1(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(X1))
    | ~ r1_tarski(u1_struct_0(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21])).

fof(c_0_47,plain,(
    ! [X31,X32] :
      ( v1_xboole_0(X31)
      | ~ m1_subset_1(X32,X31)
      | k6_domain_1(X31,X32) = k1_tarski(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_29])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_21])).

fof(c_0_53,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | m1_subset_1(k2_pre_topc(X29,X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(esk3_2(esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,esk5_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_57,plain,
    ( v2_tex_2(X3,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X2),X3,X1) != k6_domain_1(u1_struct_0(X2),esk3_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_60,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_21]),c_0_19]),c_0_20])]),c_0_17]),c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_20])])).

fof(c_0_62,plain,(
    ! [X35,X36] :
      ( ( ~ v3_tdlat_3(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ v4_pre_topc(X36,X35)
        | v3_pre_topc(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_subset_1(esk2_1(X35),k1_zfmisc_1(u1_struct_0(X35)))
        | v3_tdlat_3(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( v4_pre_topc(esk2_1(X35),X35)
        | v3_tdlat_3(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ v3_pre_topc(esk2_1(X35),X35)
        | v3_tdlat_3(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)))) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))
    | ~ v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v3_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_66,plain,(
    ! [X33,X34] :
      ( ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | v4_pre_topc(k2_pre_topc(X33,X34),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).

cnf(c_0_67,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1))) = k6_domain_1(u1_struct_0(esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_68,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)))) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))
    | ~ v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_19]),c_0_20]),c_0_61])])).

cnf(c_0_69,plain,
    ( v4_pre_topc(k2_pre_topc(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1))) = k6_domain_1(u1_struct_0(esk4_0),X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[c_0_67,c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)))) != k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_19]),c_0_20]),c_0_59])])).

cnf(c_0_72,negated_conjecture,
    ( k9_subset_1(X1,esk5_0,k2_pre_topc(esk4_0,k6_domain_1(X1,X2))) = k6_domain_1(X1,X2)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0))
    | ~ r1_tarski(u1_struct_0(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_41])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_26]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.54/1.74  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.54/1.74  # and selection function PSelectUnlessUniqMaxPos.
% 1.54/1.74  #
% 1.54/1.74  # Preprocessing time       : 0.028 s
% 1.54/1.74  # Presaturation interreduction done
% 1.54/1.74  
% 1.54/1.74  # Proof found!
% 1.54/1.74  # SZS status Theorem
% 1.54/1.74  # SZS output start CNFRefutation
% 1.54/1.74  fof(t58_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tex_2)).
% 1.54/1.74  fof(t37_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k6_domain_1(u1_struct_0(X1),X3)))))))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 1.54/1.74  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.54/1.74  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.54/1.74  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.54/1.74  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.54/1.74  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.54/1.74  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.54/1.74  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.54/1.74  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 1.54/1.74  fof(t24_tdlat_3, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v3_tdlat_3(X1)<=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X2,X1)=>v3_pre_topc(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tdlat_3)).
% 1.54/1.74  fof(fc1_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k2_pre_topc(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 1.54/1.74  fof(c_0_12, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))=>v2_tex_2(X2,X1))))), inference(assume_negation,[status(cth)],[t58_tex_2])).
% 1.54/1.74  fof(c_0_13, negated_conjecture, ![X44]:((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~m1_subset_1(X44,u1_struct_0(esk4_0))|(~r2_hidden(X44,esk5_0)|k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X44)))=k6_domain_1(u1_struct_0(esk4_0),X44)))&~v2_tex_2(esk5_0,esk4_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 1.54/1.74  fof(c_0_14, plain, ![X38, X39, X41]:((m1_subset_1(esk3_2(X38,X39),u1_struct_0(X38))|v2_tex_2(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&((r2_hidden(esk3_2(X38,X39),X39)|v2_tex_2(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X38)))|(~v3_pre_topc(X41,X38)|k9_subset_1(u1_struct_0(X38),X39,X41)!=k6_domain_1(u1_struct_0(X38),esk3_2(X38,X39)))|v2_tex_2(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t37_tex_2])])])])])])).
% 1.54/1.74  fof(c_0_15, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.54/1.74  fof(c_0_16, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.54/1.74  cnf(c_0_17, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.54/1.74  cnf(c_0_18, plain, (r2_hidden(esk3_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.54/1.74  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.54/1.74  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.54/1.74  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.54/1.74  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.54/1.74  fof(c_0_23, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.54/1.74  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.54/1.74  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.54/1.74  cnf(c_0_26, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 1.54/1.74  fof(c_0_27, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|~v1_xboole_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 1.54/1.74  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.54/1.74  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 1.54/1.74  fof(c_0_30, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(k1_tarski(X19),k1_zfmisc_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 1.54/1.74  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.54/1.74  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.54/1.74  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.54/1.74  cnf(c_0_34, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.54/1.74  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk5_0),X1)|~r1_tarski(esk5_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_31])).
% 1.54/1.74  cnf(c_0_36, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.54/1.74  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.54/1.74  cnf(c_0_38, negated_conjecture, (m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(X1))|~r1_tarski(esk5_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.54/1.74  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.54/1.74  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 1.54/1.74  cnf(c_0_41, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.54/1.74  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.54/1.74  cnf(c_0_43, negated_conjecture, (m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(X1))|~m1_subset_1(esk5_0,k1_zfmisc_1(X2))|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.54/1.74  fof(c_0_44, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|m1_subset_1(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.54/1.74  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(X1)|~r1_tarski(esk5_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 1.54/1.74  cnf(c_0_46, negated_conjecture, (m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(X1))|~r1_tarski(u1_struct_0(esk4_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_21])).
% 1.54/1.74  fof(c_0_47, plain, ![X31, X32]:(v1_xboole_0(X31)|~m1_subset_1(X32,X31)|k6_domain_1(X31,X32)=k1_tarski(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 1.54/1.74  cnf(c_0_48, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.54/1.74  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 1.54/1.74  cnf(c_0_50, negated_conjecture, (m1_subset_1(k1_tarski(esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_46, c_0_29])).
% 1.54/1.74  cnf(c_0_51, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.54/1.74  cnf(c_0_52, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_21])).
% 1.54/1.74  fof(c_0_53, plain, ![X29, X30]:(~l1_pre_topc(X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|m1_subset_1(k2_pre_topc(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 1.54/1.74  cnf(c_0_54, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_21])).
% 1.54/1.74  cnf(c_0_55, negated_conjecture, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(esk3_2(esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.54/1.74  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,esk5_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_26])).
% 1.54/1.74  cnf(c_0_57, plain, (v2_tex_2(X3,X2)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X2),X3,X1)!=k6_domain_1(u1_struct_0(X2),esk3_2(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.54/1.74  cnf(c_0_58, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.54/1.74  cnf(c_0_59, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 1.54/1.74  cnf(c_0_60, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,X1)!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))|~v3_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_21]), c_0_19]), c_0_20])]), c_0_17]), c_0_22])).
% 1.54/1.74  cnf(c_0_61, negated_conjecture, (m1_subset_1(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_20])])).
% 1.54/1.74  fof(c_0_62, plain, ![X35, X36]:((~v3_tdlat_3(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(~v4_pre_topc(X36,X35)|v3_pre_topc(X36,X35)))|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&((m1_subset_1(esk2_1(X35),k1_zfmisc_1(u1_struct_0(X35)))|v3_tdlat_3(X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&((v4_pre_topc(esk2_1(X35),X35)|v3_tdlat_3(X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~v3_pre_topc(esk2_1(X35),X35)|v3_tdlat_3(X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_tdlat_3])])])])])).
% 1.54/1.74  cnf(c_0_63, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))))!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))|~v3_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 1.54/1.74  cnf(c_0_64, plain, (v3_pre_topc(X2,X1)|~v3_tdlat_3(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.54/1.74  cnf(c_0_65, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.54/1.74  fof(c_0_66, plain, ![X33, X34]:(~v2_pre_topc(X33)|~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|v4_pre_topc(k2_pre_topc(X33,X34),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_tops_1])])).
% 1.54/1.74  cnf(c_0_67, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1)))=k6_domain_1(u1_struct_0(esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.54/1.74  cnf(c_0_68, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))))!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))|~v4_pre_topc(k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_19]), c_0_20]), c_0_61])])).
% 1.54/1.74  cnf(c_0_69, plain, (v4_pre_topc(k2_pre_topc(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.54/1.74  cnf(c_0_70, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1)))=k6_domain_1(u1_struct_0(esk4_0),X1)|~r2_hidden(X1,esk5_0)), inference(csr,[status(thm)],[c_0_67, c_0_52])).
% 1.54/1.74  cnf(c_0_71, negated_conjecture, (k9_subset_1(u1_struct_0(esk4_0),esk5_0,k2_pre_topc(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))))!=k6_domain_1(u1_struct_0(esk4_0),esk3_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_19]), c_0_20]), c_0_59])])).
% 1.54/1.74  cnf(c_0_72, negated_conjecture, (k9_subset_1(X1,esk5_0,k2_pre_topc(esk4_0,k6_domain_1(X1,X2)))=k6_domain_1(X1,X2)|~r2_hidden(X2,esk5_0)|~r1_tarski(X1,u1_struct_0(esk4_0))|~r1_tarski(u1_struct_0(esk4_0),X1)), inference(spm,[status(thm)],[c_0_70, c_0_41])).
% 1.54/1.74  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_26]), c_0_29])]), ['proof']).
% 1.54/1.74  # SZS output end CNFRefutation
% 1.54/1.74  # Proof object total steps             : 74
% 1.54/1.74  # Proof object clause steps            : 49
% 1.54/1.74  # Proof object formula steps           : 25
% 1.54/1.74  # Proof object conjectures             : 33
% 1.54/1.74  # Proof object clause conjectures      : 30
% 1.54/1.74  # Proof object formula conjectures     : 3
% 1.54/1.74  # Proof object initial clauses used    : 22
% 1.54/1.74  # Proof object initial formulas used   : 12
% 1.54/1.74  # Proof object generating inferences   : 25
% 1.54/1.74  # Proof object simplifying inferences  : 29
% 1.54/1.74  # Training examples: 0 positive, 0 negative
% 1.54/1.74  # Parsed axioms                        : 14
% 1.54/1.74  # Removed by relevancy pruning/SinE    : 0
% 1.54/1.74  # Initial clauses                      : 30
% 1.54/1.74  # Removed in clause preprocessing      : 0
% 1.54/1.74  # Initial clauses in saturation        : 30
% 1.54/1.74  # Processed clauses                    : 8451
% 1.54/1.74  # ...of these trivial                  : 23
% 1.54/1.74  # ...subsumed                          : 4869
% 1.54/1.74  # ...remaining for further processing  : 3559
% 1.54/1.74  # Other redundant clauses eliminated   : 715
% 1.54/1.74  # Clauses deleted for lack of memory   : 0
% 1.54/1.74  # Backward-subsumed                    : 210
% 1.54/1.74  # Backward-rewritten                   : 8
% 1.54/1.74  # Generated clauses                    : 103907
% 1.54/1.74  # ...of the previous two non-trivial   : 100050
% 1.54/1.74  # Contextual simplify-reflections      : 36
% 1.54/1.74  # Paramodulations                      : 103180
% 1.54/1.74  # Factorizations                       : 12
% 1.54/1.74  # Equation resolutions                 : 715
% 1.54/1.74  # Propositional unsat checks           : 0
% 1.54/1.74  #    Propositional check models        : 0
% 1.54/1.74  #    Propositional check unsatisfiable : 0
% 1.54/1.74  #    Propositional clauses             : 0
% 1.54/1.74  #    Propositional clauses after purity: 0
% 1.54/1.74  #    Propositional unsat core size     : 0
% 1.54/1.74  #    Propositional preprocessing time  : 0.000
% 1.54/1.74  #    Propositional encoding time       : 0.000
% 1.54/1.74  #    Propositional solver time         : 0.000
% 1.54/1.74  #    Success case prop preproc time    : 0.000
% 1.54/1.74  #    Success case prop encoding time   : 0.000
% 1.54/1.74  #    Success case prop solver time     : 0.000
% 1.54/1.74  # Current number of processed clauses  : 3310
% 1.54/1.74  #    Positive orientable unit clauses  : 71
% 1.54/1.74  #    Positive unorientable unit clauses: 0
% 1.54/1.74  #    Negative unit clauses             : 90
% 1.54/1.74  #    Non-unit-clauses                  : 3149
% 1.54/1.74  # Current number of unprocessed clauses: 91443
% 1.54/1.74  # ...number of literals in the above   : 427680
% 1.54/1.74  # Current number of archived formulas  : 0
% 1.54/1.74  # Current number of archived clauses   : 247
% 1.54/1.74  # Clause-clause subsumption calls (NU) : 1823806
% 1.54/1.74  # Rec. Clause-clause subsumption calls : 249899
% 1.54/1.74  # Non-unit clause-clause subsumptions  : 3762
% 1.54/1.74  # Unit Clause-clause subsumption calls : 53853
% 1.54/1.74  # Rewrite failures with RHS unbound    : 0
% 1.54/1.74  # BW rewrite match attempts            : 1134
% 1.54/1.74  # BW rewrite match successes           : 9
% 1.54/1.74  # Condensation attempts                : 0
% 1.54/1.74  # Condensation successes               : 0
% 1.54/1.74  # Termbank termtop insertions          : 2963074
% 1.54/1.75  
% 1.54/1.75  # -------------------------------------------------
% 1.54/1.75  # User time                : 1.343 s
% 1.54/1.75  # System time              : 0.049 s
% 1.54/1.75  # Total time               : 1.392 s
% 1.54/1.75  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
