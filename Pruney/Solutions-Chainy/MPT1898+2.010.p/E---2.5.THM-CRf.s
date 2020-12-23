%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:55 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 322 expanded)
%              Number of clauses        :   37 ( 141 expanded)
%              Number of leaves         :   11 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          :  211 ( 997 expanded)
%              Number of equality atoms :   13 ( 114 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   21 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t65_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ~ ( r1_tarski(X2,X3)
                      & v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(t66_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(t58_tex_2,axiom,(
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

fof(c_0_11,plain,(
    ! [X16] : ~ v1_xboole_0(k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_12,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | m1_subset_1(X20,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,plain,(
    ! [X17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_15,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_18,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | r1_tarski(X11,X9)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r1_tarski(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r1_tarski(esk2_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(esk2_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( ~ r1_tarski(k1_zfmisc_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( ~ r1_tarski(esk2_2(X1,X2),X1)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_16])).

fof(c_0_28,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_29,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(esk2_2(X2,X1),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_16])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_tarski(esk2_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( ~ r1_tarski(esk2_2(X1,X2),X3)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r1_tarski(esk2_2(X1,X2),X1)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_31]),c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(esk2_2(X1,X2),X1)
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( r1_tarski(esk2_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_17])).

fof(c_0_38,plain,(
    ! [X29,X30] :
      ( ( m1_subset_1(esk4_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ v3_tdlat_3(X29)
        | ~ l1_pre_topc(X29) )
      & ( r1_tarski(X30,esk4_2(X29,X30))
        | ~ v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ v3_tdlat_3(X29)
        | ~ l1_pre_topc(X29) )
      & ( v3_tex_2(esk4_2(X29,X30),X29)
        | ~ v2_tex_2(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ v3_tdlat_3(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_39,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X1,esk2_2(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ? [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v3_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t66_tex_2])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_42,plain,(
    ! [X26,X27] :
      ( ( m1_subset_1(esk3_2(X26,X27),u1_struct_0(X26))
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ v3_tdlat_3(X26)
        | ~ l1_pre_topc(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ v3_tdlat_3(X26)
        | ~ l1_pre_topc(X26) )
      & ( k9_subset_1(u1_struct_0(X26),X27,k2_pre_topc(X26,k6_domain_1(u1_struct_0(X26),esk3_2(X26,X27)))) != k6_domain_1(u1_struct_0(X26),esk3_2(X26,X27))
        | v2_tex_2(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ v3_tdlat_3(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t58_tex_2])])])])])])).

cnf(c_0_43,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_37])])).

fof(c_0_44,negated_conjecture,(
    ! [X33] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & v3_tdlat_3(esk5_0)
      & l1_pre_topc(esk5_0)
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | ~ v3_tex_2(X33,esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_46,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_26]),c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_20])]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( v3_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_tex_2(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk4_2(esk5_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v3_tex_2(esk4_2(esk5_0,k1_xboole_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,plain,
    ( v3_tex_2(esk4_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_tex_2(k1_xboole_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_50]),c_0_51]),c_0_52]),c_0_20])]),c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_50]),c_0_51]),c_0_52]),c_0_20])]),c_0_48]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.73/0.92  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.73/0.92  # and selection function PSelectUnlessUniqMaxPos.
% 0.73/0.92  #
% 0.73/0.92  # Preprocessing time       : 0.022 s
% 0.73/0.92  # Presaturation interreduction done
% 0.73/0.92  
% 0.73/0.92  # Proof found!
% 0.73/0.92  # SZS status Theorem
% 0.73/0.92  # SZS output start CNFRefutation
% 0.73/0.92  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.73/0.92  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.73/0.92  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.73/0.92  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.73/0.92  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.73/0.92  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.73/0.92  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.73/0.92  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.73/0.92  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 0.73/0.92  fof(t66_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 0.73/0.92  fof(t58_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,X2)=>k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,k6_domain_1(u1_struct_0(X1),X3)))=k6_domain_1(u1_struct_0(X1),X3)))=>v2_tex_2(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_tex_2)).
% 0.73/0.92  fof(c_0_11, plain, ![X16]:~v1_xboole_0(k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.73/0.92  fof(c_0_12, plain, ![X8]:(~r1_tarski(X8,k1_xboole_0)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.73/0.92  fof(c_0_13, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|m1_subset_1(X20,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.73/0.92  fof(c_0_14, plain, ![X17]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X17)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.73/0.92  cnf(c_0_15, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.73/0.92  cnf(c_0_16, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.73/0.92  cnf(c_0_17, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.73/0.92  fof(c_0_18, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X11,X10)|r1_tarski(X11,X9)|X10!=k1_zfmisc_1(X9))&(~r1_tarski(X12,X9)|r2_hidden(X12,X10)|X10!=k1_zfmisc_1(X9)))&((~r2_hidden(esk2_2(X13,X14),X14)|~r1_tarski(esk2_2(X13,X14),X13)|X14=k1_zfmisc_1(X13))&(r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(esk2_2(X13,X14),X13)|X14=k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.73/0.92  cnf(c_0_19, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.73/0.92  cnf(c_0_20, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.73/0.92  cnf(c_0_21, plain, (~r1_tarski(k1_zfmisc_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.73/0.92  cnf(c_0_22, plain, (X2=k1_zfmisc_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r1_tarski(esk2_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.73/0.92  fof(c_0_23, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.73/0.92  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.73/0.92  cnf(c_0_25, plain, (~r1_tarski(esk2_2(X1,X2),X1)|~r1_tarski(X2,k1_xboole_0)|~r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.73/0.92  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.73/0.92  cnf(c_0_27, plain, (m1_subset_1(X1,X2)|~r1_tarski(X3,k1_xboole_0)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_16])).
% 0.73/0.92  fof(c_0_28, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.73/0.92  cnf(c_0_29, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(esk2_2(X2,X1),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.73/0.92  cnf(c_0_30, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_16])).
% 0.73/0.92  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_tarski(esk2_2(X1,X2),X1)|X2=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.73/0.92  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.73/0.92  cnf(c_0_33, plain, (~r1_tarski(esk2_2(X1,X2),X3)|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X3,k1_xboole_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.73/0.92  cnf(c_0_34, plain, (r1_tarski(esk2_2(X1,X2),X1)|~r1_tarski(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_31]), c_0_29])).
% 0.73/0.92  cnf(c_0_35, plain, (r1_tarski(esk2_2(X1,X2),X1)|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_31]), c_0_32])).
% 0.73/0.92  cnf(c_0_36, plain, (~r1_tarski(X1,k1_xboole_0)|~r1_tarski(X2,k1_xboole_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.73/0.92  cnf(c_0_37, plain, (r1_tarski(esk2_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_35, c_0_17])).
% 0.73/0.92  fof(c_0_38, plain, ![X29, X30]:((m1_subset_1(esk4_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))|~v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~v3_tdlat_3(X29)|~l1_pre_topc(X29)))&((r1_tarski(X30,esk4_2(X29,X30))|~v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~v3_tdlat_3(X29)|~l1_pre_topc(X29)))&(v3_tex_2(esk4_2(X29,X30),X29)|~v2_tex_2(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~v3_tdlat_3(X29)|~l1_pre_topc(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.73/0.92  cnf(c_0_39, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(X1,esk2_2(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.73/0.92  fof(c_0_40, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&v3_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t66_tex_2])).
% 0.73/0.92  cnf(c_0_41, plain, (m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.73/0.92  fof(c_0_42, plain, ![X26, X27]:((m1_subset_1(esk3_2(X26,X27),u1_struct_0(X26))|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~v3_tdlat_3(X26)|~l1_pre_topc(X26)))&((r2_hidden(esk3_2(X26,X27),X27)|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~v3_tdlat_3(X26)|~l1_pre_topc(X26)))&(k9_subset_1(u1_struct_0(X26),X27,k2_pre_topc(X26,k6_domain_1(u1_struct_0(X26),esk3_2(X26,X27))))!=k6_domain_1(u1_struct_0(X26),esk3_2(X26,X27))|v2_tex_2(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~v3_tdlat_3(X26)|~l1_pre_topc(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t58_tex_2])])])])])])).
% 0.73/0.92  cnf(c_0_43, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_37])])).
% 0.73/0.92  fof(c_0_44, negated_conjecture, ![X33]:((((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&v3_tdlat_3(esk5_0))&l1_pre_topc(esk5_0))&(~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_tex_2(X33,esk5_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])])).
% 0.73/0.92  cnf(c_0_45, plain, (v2_struct_0(X1)|m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_20])).
% 0.73/0.92  cnf(c_0_46, plain, (r2_hidden(esk3_2(X1,X2),X2)|v2_tex_2(X2,X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.73/0.92  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_26]), c_0_24])).
% 0.73/0.92  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.73/0.92  cnf(c_0_49, plain, (v2_struct_0(X1)|m1_subset_1(esk4_2(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~v3_tdlat_3(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_20])]), c_0_47])).
% 0.73/0.92  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.73/0.92  cnf(c_0_51, negated_conjecture, (v3_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.73/0.92  cnf(c_0_52, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.73/0.92  cnf(c_0_53, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_tex_2(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.73/0.92  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk4_2(esk5_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52])])).
% 0.73/0.92  cnf(c_0_55, negated_conjecture, (~v3_tex_2(esk4_2(esk5_0,k1_xboole_0),esk5_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.73/0.92  cnf(c_0_56, plain, (v3_tex_2(esk4_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.73/0.92  cnf(c_0_57, negated_conjecture, (~v2_tex_2(k1_xboole_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_50]), c_0_51]), c_0_52]), c_0_20])]), c_0_48])).
% 0.73/0.92  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_50]), c_0_51]), c_0_52]), c_0_20])]), c_0_48]), c_0_47]), ['proof']).
% 0.73/0.92  # SZS output end CNFRefutation
% 0.73/0.92  # Proof object total steps             : 59
% 0.73/0.92  # Proof object clause steps            : 37
% 0.73/0.92  # Proof object formula steps           : 22
% 0.73/0.92  # Proof object conjectures             : 12
% 0.73/0.92  # Proof object clause conjectures      : 9
% 0.73/0.92  # Proof object formula conjectures     : 3
% 0.73/0.92  # Proof object initial clauses used    : 17
% 0.73/0.92  # Proof object initial formulas used   : 11
% 0.73/0.92  # Proof object generating inferences   : 20
% 0.73/0.92  # Proof object simplifying inferences  : 28
% 0.73/0.92  # Training examples: 0 positive, 0 negative
% 0.73/0.92  # Parsed axioms                        : 12
% 0.73/0.92  # Removed by relevancy pruning/SinE    : 0
% 0.73/0.92  # Initial clauses                      : 25
% 0.73/0.92  # Removed in clause preprocessing      : 0
% 0.73/0.92  # Initial clauses in saturation        : 25
% 0.73/0.92  # Processed clauses                    : 4238
% 0.73/0.92  # ...of these trivial                  : 33
% 0.73/0.92  # ...subsumed                          : 3099
% 0.73/0.92  # ...remaining for further processing  : 1106
% 0.73/0.92  # Other redundant clauses eliminated   : 181
% 0.73/0.92  # Clauses deleted for lack of memory   : 0
% 0.73/0.92  # Backward-subsumed                    : 89
% 0.73/0.92  # Backward-rewritten                   : 1
% 0.73/0.92  # Generated clauses                    : 56242
% 0.73/0.92  # ...of the previous two non-trivial   : 51114
% 0.73/0.92  # Contextual simplify-reflections      : 11
% 0.73/0.92  # Paramodulations                      : 56061
% 0.73/0.92  # Factorizations                       : 0
% 0.73/0.92  # Equation resolutions                 : 181
% 0.73/0.92  # Propositional unsat checks           : 0
% 0.73/0.92  #    Propositional check models        : 0
% 0.73/0.92  #    Propositional check unsatisfiable : 0
% 0.73/0.92  #    Propositional clauses             : 0
% 0.73/0.92  #    Propositional clauses after purity: 0
% 0.73/0.92  #    Propositional unsat core size     : 0
% 0.73/0.92  #    Propositional preprocessing time  : 0.000
% 0.73/0.92  #    Propositional encoding time       : 0.000
% 0.73/0.92  #    Propositional solver time         : 0.000
% 0.73/0.92  #    Success case prop preproc time    : 0.000
% 0.73/0.92  #    Success case prop encoding time   : 0.000
% 0.73/0.92  #    Success case prop solver time     : 0.000
% 0.73/0.92  # Current number of processed clauses  : 989
% 0.73/0.92  #    Positive orientable unit clauses  : 52
% 0.73/0.92  #    Positive unorientable unit clauses: 0
% 0.73/0.92  #    Negative unit clauses             : 75
% 0.73/0.92  #    Non-unit-clauses                  : 862
% 0.73/0.92  # Current number of unprocessed clauses: 46743
% 0.73/0.92  # ...number of literals in the above   : 264556
% 0.73/0.92  # Current number of archived formulas  : 0
% 0.73/0.92  # Current number of archived clauses   : 115
% 0.73/0.92  # Clause-clause subsumption calls (NU) : 216964
% 0.73/0.92  # Rec. Clause-clause subsumption calls : 39337
% 0.73/0.92  # Non-unit clause-clause subsumptions  : 2001
% 0.73/0.92  # Unit Clause-clause subsumption calls : 6313
% 0.73/0.92  # Rewrite failures with RHS unbound    : 0
% 0.73/0.92  # BW rewrite match attempts            : 99
% 0.73/0.92  # BW rewrite match successes           : 2
% 0.73/0.92  # Condensation attempts                : 0
% 0.73/0.92  # Condensation successes               : 0
% 0.73/0.92  # Termbank termtop insertions          : 984931
% 0.73/0.92  
% 0.73/0.92  # -------------------------------------------------
% 0.73/0.92  # User time                : 0.558 s
% 0.73/0.92  # System time              : 0.022 s
% 0.73/0.92  # Total time               : 0.581 s
% 0.73/0.92  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
