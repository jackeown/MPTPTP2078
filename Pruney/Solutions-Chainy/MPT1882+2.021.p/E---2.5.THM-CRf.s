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
% DateTime   : Thu Dec  3 11:20:39 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 455 expanded)
%              Number of clauses        :   39 ( 160 expanded)
%              Number of leaves         :   10 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  255 (3031 expanded)
%              Number of equality atoms :   24 (  58 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   31 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_tex_2,axiom,(
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

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(cc1_zfmisc_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_zfmisc_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(t50_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v3_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(d7_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tex_2(X2,X1)
          <=> ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(l48_tex_2,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & X1 != X2
        & k6_subset_1(X2,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_tex_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k6_subset_1,axiom,(
    ! [X1,X2] : m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(c_0_10,plain,(
    ! [X28,X29] :
      ( ( ~ v2_tex_2(X29,X28)
        | v1_zfmisc_1(X29)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v1_zfmisc_1(X29)
        | v2_tex_2(X29,X28)
        | v1_xboole_0(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_tex_2])])])])])).

fof(c_0_11,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | ~ v2_tdlat_3(X19)
      | v2_pre_topc(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

fof(c_0_12,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | v1_zfmisc_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v3_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tex_2])).

cnf(c_0_14,plain,
    ( v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_zfmisc_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v2_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ( ~ v3_tex_2(esk4_0,esk3_0)
      | ~ v1_zfmisc_1(esk4_0) )
    & ( v3_tex_2(esk4_0,esk3_0)
      | v1_zfmisc_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] :
      ( ( v2_tex_2(X21,X20)
        | ~ v3_tex_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ v2_tex_2(X22,X20)
        | ~ r1_tarski(X21,X22)
        | X21 = X22
        | ~ v3_tex_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ v2_tex_2(X21,X20)
        | v3_tex_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( v2_tex_2(esk2_2(X20,X21),X20)
        | ~ v2_tex_2(X21,X20)
        | v3_tex_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( r1_tarski(X21,esk2_2(X20,X21))
        | ~ v2_tex_2(X21,X20)
        | v3_tex_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( X21 != esk2_2(X20,X21)
        | ~ v2_tex_2(X21,X20)
        | v3_tex_2(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

cnf(c_0_19,plain,
    ( v2_tex_2(X1,X2)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v1_zfmisc_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v2_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v2_tex_2(X1,X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | X24 = X25
      | k6_subset_1(X25,X24) != k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l48_tex_2])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(X2,X1)
    | v1_xboole_0(X2)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_zfmisc_1(X2) ),
    inference(csr,[status(thm)],[c_0_19,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v1_zfmisc_1(esk4_0)
    | ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0)
    | ~ v3_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( v3_tex_2(esk4_0,esk3_0)
    | v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_33,plain,(
    ! [X8,X9] : m1_subset_1(k6_subset_1(X8,X9),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k6_subset_1])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | k6_subset_1(X2,X1) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,esk2_2(X2,X1))
    | v3_tex_2(X1,X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( v3_tex_2(X1,X2)
    | X1 != esk2_2(X2,X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0)
    | ~ v1_zfmisc_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v1_zfmisc_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( ~ v3_tex_2(esk4_0,esk3_0)
    | ~ v1_zfmisc_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_42,plain,(
    ! [X13,X15,X16,X17,X18] :
      ( ( r2_hidden(esk1_1(X13),X13)
        | X13 = k1_xboole_0 )
      & ( ~ r2_hidden(X15,X13)
        | esk1_1(X13) != k4_mcart_1(X15,X16,X17,X18)
        | X13 = k1_xboole_0 )
      & ( ~ r2_hidden(X16,X13)
        | esk1_1(X13) != k4_mcart_1(X15,X16,X17,X18)
        | X13 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_43,plain,(
    ! [X26,X27] :
      ( v1_xboole_0(X26)
      | v1_xboole_0(X27)
      | ~ v1_zfmisc_1(X27)
      | ~ r1_tarski(X26,X27)
      | X26 = X27 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_44,plain,
    ( v3_tex_2(X1,X2)
    | k6_subset_1(esk2_2(X2,X1),X1) != k1_xboole_0
    | ~ v2_tex_2(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( ~ v3_tex_2(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k6_subset_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k6_subset_1(esk2_2(esk3_0,esk4_0),esk4_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_21]),c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_51,plain,
    ( k6_subset_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( v3_tex_2(X1,X2)
    | v1_xboole_0(esk2_2(X2,X1))
    | v1_xboole_0(X1)
    | ~ v2_tex_2(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_zfmisc_1(esk2_2(X2,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_36])).

cnf(c_0_53,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,plain,
    ( v2_tex_2(esk2_2(X1,X2),X1)
    | v3_tex_2(X2,X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk2_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk2_2(esk3_0,esk4_0))
    | ~ v1_zfmisc_1(esk2_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_21]),c_0_45]),c_0_23])]),c_0_46]),c_0_28])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v3_tex_2(X2,X1)
    | v1_zfmisc_1(esk2_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_53]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_zfmisc_1(esk2_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_21]),c_0_45]),c_0_22]),c_0_23])]),c_0_24]),c_0_46]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:16:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t44_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.14/0.38  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.14/0.38  fof(cc1_zfmisc_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 0.14/0.38  fof(t50_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v3_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 0.14/0.38  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 0.14/0.38  fof(l48_tex_2, axiom, ![X1, X2]:~(((r1_tarski(X1,X2)&X1!=X2)&k6_subset_1(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l48_tex_2)).
% 0.14/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.38  fof(dt_k6_subset_1, axiom, ![X1, X2]:m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 0.14/0.38  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.14/0.38  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.14/0.38  fof(c_0_10, plain, ![X28, X29]:((~v2_tex_2(X29,X28)|v1_zfmisc_1(X29)|(v1_xboole_0(X29)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v2_tdlat_3(X28)|~l1_pre_topc(X28)))&(~v1_zfmisc_1(X29)|v2_tex_2(X29,X28)|(v1_xboole_0(X29)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v2_tdlat_3(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t44_tex_2])])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X19]:(~l1_pre_topc(X19)|(~v2_tdlat_3(X19)|v2_pre_topc(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.14/0.38  fof(c_0_12, plain, ![X7]:(~v1_xboole_0(X7)|v1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_zfmisc_1])])).
% 0.14/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v3_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t50_tex_2])).
% 0.14/0.38  cnf(c_0_14, plain, (v1_zfmisc_1(X1)|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_15, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_16, plain, (v1_zfmisc_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_17, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v2_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))))&((~v3_tex_2(esk4_0,esk3_0)|~v1_zfmisc_1(esk4_0))&(v3_tex_2(esk4_0,esk3_0)|v1_zfmisc_1(esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.14/0.38  fof(c_0_18, plain, ![X20, X21, X22]:(((v2_tex_2(X21,X20)|~v3_tex_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~v2_tex_2(X22,X20)|~r1_tarski(X21,X22)|X21=X22)|~v3_tex_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20)))&((m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|~v2_tex_2(X21,X20)|v3_tex_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(((v2_tex_2(esk2_2(X20,X21),X20)|~v2_tex_2(X21,X20)|v3_tex_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(r1_tarski(X21,esk2_2(X20,X21))|~v2_tex_2(X21,X20)|v3_tex_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20)))&(X21!=esk2_2(X20,X21)|~v2_tex_2(X21,X20)|v3_tex_2(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 0.14/0.38  cnf(c_0_19, plain, (v2_tex_2(X1,X2)|v1_xboole_0(X1)|v2_struct_0(X2)|~v1_zfmisc_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_20, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (v2_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_25, plain, (v2_tex_2(X1,X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  fof(c_0_26, plain, ![X24, X25]:(~r1_tarski(X24,X25)|X24=X25|k6_subset_1(X25,X24)!=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l48_tex_2])])).
% 0.14/0.38  cnf(c_0_27, plain, (v2_struct_0(X1)|v2_tex_2(X2,X1)|v1_xboole_0(X2)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_zfmisc_1(X2)), inference(csr,[status(thm)],[c_0_19, c_0_15])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (v1_zfmisc_1(esk4_0)|~v2_tex_2(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)|~v3_tex_2(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_23])])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (v3_tex_2(esk4_0,esk3_0)|v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  fof(c_0_32, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.38  fof(c_0_33, plain, ![X8, X9]:m1_subset_1(k6_subset_1(X8,X9),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k6_subset_1])).
% 0.14/0.38  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|k6_subset_1(X2,X1)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_35, plain, (r1_tarski(X1,esk2_2(X2,X1))|v3_tex_2(X1,X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_36, plain, (v3_tex_2(X1,X2)|X1!=esk2_2(X2,X1)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)|~v1_zfmisc_1(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_28])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (v1_zfmisc_1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (~v3_tex_2(esk4_0,esk3_0)|~v1_zfmisc_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  cnf(c_0_41, plain, (m1_subset_1(k6_subset_1(X1,X2),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  fof(c_0_42, plain, ![X13, X15, X16, X17, X18]:((r2_hidden(esk1_1(X13),X13)|X13=k1_xboole_0)&((~r2_hidden(X15,X13)|esk1_1(X13)!=k4_mcart_1(X15,X16,X17,X18)|X13=k1_xboole_0)&(~r2_hidden(X16,X13)|esk1_1(X13)!=k4_mcart_1(X15,X16,X17,X18)|X13=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.14/0.38  fof(c_0_43, plain, ![X26, X27]:(v1_xboole_0(X26)|(v1_xboole_0(X27)|~v1_zfmisc_1(X27)|(~r1_tarski(X26,X27)|X26=X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.14/0.38  cnf(c_0_44, plain, (v3_tex_2(X1,X2)|k6_subset_1(esk2_2(X2,X1),X1)!=k1_xboole_0|~v2_tex_2(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (~v3_tex_2(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38])])).
% 0.14/0.38  cnf(c_0_47, plain, (~r2_hidden(X1,k6_subset_1(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.38  cnf(c_0_48, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_49, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (k6_subset_1(esk2_2(esk3_0,esk4_0),esk4_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_21]), c_0_45]), c_0_23])]), c_0_46])).
% 0.14/0.38  cnf(c_0_51, plain, (k6_subset_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.38  cnf(c_0_52, plain, (v3_tex_2(X1,X2)|v1_xboole_0(esk2_2(X2,X1))|v1_xboole_0(X1)|~v2_tex_2(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v1_zfmisc_1(esk2_2(X2,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_35]), c_0_36])).
% 0.14/0.38  cnf(c_0_53, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_54, plain, (v2_tex_2(esk2_2(X1,X2),X1)|v3_tex_2(X2,X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk2_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (v1_xboole_0(esk2_2(esk3_0,esk4_0))|~v1_zfmisc_1(esk2_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_21]), c_0_45]), c_0_23])]), c_0_46]), c_0_28])).
% 0.14/0.38  cnf(c_0_57, plain, (v2_struct_0(X1)|v3_tex_2(X2,X1)|v1_zfmisc_1(esk2_2(X1,X2))|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_53]), c_0_54])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (~v1_zfmisc_1(esk2_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_21]), c_0_45]), c_0_22]), c_0_23])]), c_0_24]), c_0_46]), c_0_58]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 60
% 0.14/0.38  # Proof object clause steps            : 39
% 0.14/0.38  # Proof object formula steps           : 21
% 0.14/0.38  # Proof object conjectures             : 21
% 0.14/0.38  # Proof object clause conjectures      : 18
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 21
% 0.14/0.38  # Proof object initial formulas used   : 10
% 0.14/0.38  # Proof object generating inferences   : 14
% 0.14/0.38  # Proof object simplifying inferences  : 38
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 25
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 25
% 0.14/0.38  # Processed clauses                    : 94
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 19
% 0.14/0.38  # ...remaining for further processing  : 75
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 4
% 0.14/0.38  # Backward-rewritten                   : 4
% 0.14/0.38  # Generated clauses                    : 95
% 0.14/0.38  # ...of the previous two non-trivial   : 85
% 0.14/0.38  # Contextual simplify-reflections      : 12
% 0.14/0.38  # Paramodulations                      : 95
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 67
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 7
% 0.14/0.38  #    Non-unit-clauses                  : 53
% 0.14/0.38  # Current number of unprocessed clauses: 14
% 0.14/0.38  # ...number of literals in the above   : 110
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 8
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1318
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 186
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 33
% 0.14/0.38  # Unit Clause-clause subsumption calls : 12
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 4394
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.038 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
