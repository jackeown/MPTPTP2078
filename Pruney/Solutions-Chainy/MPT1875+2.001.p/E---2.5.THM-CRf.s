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
% DateTime   : Thu Dec  3 11:20:12 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 448 expanded)
%              Number of clauses        :   47 ( 166 expanded)
%              Number of leaves         :   16 ( 111 expanded)
%              Depth                    :   13
%              Number of atoms          :  301 (2095 expanded)
%              Number of equality atoms :   27 (  79 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => v2_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(cc5_tdlat_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v1_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_borsuk_1(X2,X1)
            & v1_tsep_1(X2,X1)
            & v1_tdlat_3(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(cc1_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(t10_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & X2 = u1_struct_0(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t27_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( X2 = u1_struct_0(X1)
           => ( v2_tex_2(X2,X1)
            <=> v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t29_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_tex_2(X2,X1)
                  | v2_tex_2(X3,X1) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => v2_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t43_tex_2])).

fof(c_0_17,plain,(
    ! [X32,X33] :
      ( ( v1_borsuk_1(X33,X32)
        | ~ m1_pre_topc(X33,X32)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ v1_tdlat_3(X32)
        | ~ l1_pre_topc(X32) )
      & ( v1_tsep_1(X33,X32)
        | ~ m1_pre_topc(X33,X32)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ v1_tdlat_3(X32)
        | ~ l1_pre_topc(X32) )
      & ( v1_tdlat_3(X33)
        | ~ m1_pre_topc(X33,X32)
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ v1_tdlat_3(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_tdlat_3])])])])])).

fof(c_0_18,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | ~ v1_tdlat_3(X31)
      | v2_pre_topc(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).

fof(c_0_19,plain,(
    ! [X34,X35] :
      ( ( ~ v2_struct_0(esk2_2(X34,X35))
        | v1_xboole_0(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34) )
      & ( v1_pre_topc(esk2_2(X34,X35))
        | v1_xboole_0(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34) )
      & ( m1_pre_topc(esk2_2(X34,X35),X34)
        | v1_xboole_0(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34) )
      & ( X35 = u1_struct_0(esk2_2(X34,X35))
        | v1_xboole_0(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ l1_pre_topc(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & v1_tdlat_3(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v2_tex_2(X39,X37)
        | v1_tdlat_3(X38)
        | X39 != u1_struct_0(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | v2_struct_0(X38)
        | ~ m1_pre_topc(X38,X37)
        | v2_struct_0(X37)
        | ~ l1_pre_topc(X37) )
      & ( ~ v1_tdlat_3(X38)
        | v2_tex_2(X39,X37)
        | X39 != u1_struct_0(X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))
        | v2_struct_0(X38)
        | ~ m1_pre_topc(X38,X37)
        | v2_struct_0(X37)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_22,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | m1_subset_1(u1_struct_0(X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_23,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_pre_topc(esk2_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X13] : m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_30,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_31,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | v1_tdlat_3(X2)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk2_2(esk3_0,esk4_0),esk3_0)
    | v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_36,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_tdlat_3(esk2_2(esk3_0,esk4_0))
    | v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_27])]),c_0_28])).

cnf(c_0_41,plain,
    ( X1 = u1_struct_0(esk2_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk2_2(esk3_0,esk4_0)),esk3_0)
    | v2_struct_0(esk2_2(esk3_0,esk4_0))
    | v1_xboole_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_27])]),c_0_28]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk2_2(esk3_0,esk4_0)) = esk4_0
    | v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_48,plain,(
    ! [X40,X41] :
      ( ( ~ v2_tex_2(X41,X40)
        | v1_tdlat_3(X40)
        | X41 != u1_struct_0(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ l1_pre_topc(X40) )
      & ( ~ v1_tdlat_3(X40)
        | v2_tex_2(X41,X40)
        | X41 != u1_struct_0(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | v2_struct_0(X40)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tex_2])])])])])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( v2_struct_0(esk2_2(esk3_0,esk4_0))
    | v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_53,plain,
    ( v2_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_27]),c_0_26])]),c_0_28])).

fof(c_0_57,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k3_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_58,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_59,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v2_tex_2(X43,X42)
        | v2_tex_2(k9_subset_1(u1_struct_0(X42),X43,X44),X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X42) )
      & ( ~ v2_tex_2(X44,X42)
        | v2_tex_2(k9_subset_1(u1_struct_0(X42),X43,X44),X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tex_2])])])])).

cnf(c_0_60,plain,
    ( v2_tex_2(u1_struct_0(X1),X1)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_43])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_64,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_65,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( v2_tex_2(k9_subset_1(u1_struct_0(X2),X1,X3),X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_35]),c_0_27])]),c_0_28])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(X1,esk4_0) = k9_subset_1(u1_struct_0(esk3_0),X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_26])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_72,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_43])).

cnf(c_0_73,negated_conjecture,
    ( v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_27]),c_0_43])])).

cnf(c_0_74,negated_conjecture,
    ( k9_subset_1(X1,X2,esk4_0) = k9_subset_1(u1_struct_0(esk3_0),X2,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_68]),c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( X1 = esk4_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_62])).

cnf(c_0_76,plain,
    ( r1_tarski(k9_subset_1(X1,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( v2_tex_2(k9_subset_1(X1,u1_struct_0(esk3_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_68])])).

cnf(c_0_78,negated_conjecture,
    ( k9_subset_1(esk4_0,X1,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.13/0.39  # and selection function PSelectComplexPreferEQ.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.029 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t43_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 0.13/0.39  fof(cc5_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((v1_borsuk_1(X2,X1)&v1_tsep_1(X2,X1))&v1_tdlat_3(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 0.13/0.39  fof(cc1_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tdlat_3)).
% 0.13/0.39  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.13/0.39  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 0.13/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(t27_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(X2=u1_struct_0(X1)=>(v2_tex_2(X2,X1)<=>v1_tdlat_3(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.13/0.39  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.13/0.39  fof(t29_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>v2_tex_2(X2,X1)))), inference(assume_negation,[status(cth)],[t43_tex_2])).
% 0.13/0.39  fof(c_0_17, plain, ![X32, X33]:(((v1_borsuk_1(X33,X32)|~m1_pre_topc(X33,X32)|(v2_struct_0(X32)|~v2_pre_topc(X32)|~v1_tdlat_3(X32)|~l1_pre_topc(X32)))&(v1_tsep_1(X33,X32)|~m1_pre_topc(X33,X32)|(v2_struct_0(X32)|~v2_pre_topc(X32)|~v1_tdlat_3(X32)|~l1_pre_topc(X32))))&(v1_tdlat_3(X33)|~m1_pre_topc(X33,X32)|(v2_struct_0(X32)|~v2_pre_topc(X32)|~v1_tdlat_3(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_tdlat_3])])])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X31]:(~l1_pre_topc(X31)|(~v1_tdlat_3(X31)|v2_pre_topc(X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_tdlat_3])])).
% 0.13/0.39  fof(c_0_19, plain, ![X34, X35]:((((~v2_struct_0(esk2_2(X34,X35))|(v1_xboole_0(X35)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))))|(v2_struct_0(X34)|~l1_pre_topc(X34)))&(v1_pre_topc(esk2_2(X34,X35))|(v1_xboole_0(X35)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))))|(v2_struct_0(X34)|~l1_pre_topc(X34))))&(m1_pre_topc(esk2_2(X34,X35),X34)|(v1_xboole_0(X35)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))))|(v2_struct_0(X34)|~l1_pre_topc(X34))))&(X35=u1_struct_0(esk2_2(X34,X35))|(v1_xboole_0(X35)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34))))|(v2_struct_0(X34)|~l1_pre_topc(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.13/0.39  fof(c_0_20, negated_conjecture, ((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v1_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&~v2_tex_2(esk4_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.13/0.39  fof(c_0_21, plain, ![X37, X38, X39]:((~v2_tex_2(X39,X37)|v1_tdlat_3(X38)|X39!=u1_struct_0(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X38)|~m1_pre_topc(X38,X37))|(v2_struct_0(X37)|~l1_pre_topc(X37)))&(~v1_tdlat_3(X38)|v2_tex_2(X39,X37)|X39!=u1_struct_0(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X37)))|(v2_struct_0(X38)|~m1_pre_topc(X38,X37))|(v2_struct_0(X37)|~l1_pre_topc(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.13/0.39  fof(c_0_22, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|m1_subset_1(u1_struct_0(X30),k1_zfmisc_1(u1_struct_0(X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.39  cnf(c_0_23, plain, (v1_tdlat_3(X1)|v2_struct_0(X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v1_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_24, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_25, plain, (m1_pre_topc(esk2_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  fof(c_0_29, plain, ![X13]:m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.39  fof(c_0_30, plain, ![X12]:k2_subset_1(X12)=X12, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.39  cnf(c_0_31, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.39  cnf(c_0_32, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.39  cnf(c_0_33, plain, (v2_struct_0(X1)|v1_tdlat_3(X2)|~v1_tdlat_3(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk2_2(esk3_0,esk4_0),esk3_0)|v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_28])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (v1_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  fof(c_0_36, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.13/0.39  cnf(c_0_37, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_38, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.39  cnf(c_0_39, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_31]), c_0_32])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (v1_tdlat_3(esk2_2(esk3_0,esk4_0))|v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_27])]), c_0_28])).
% 0.13/0.39  cnf(c_0_41, plain, (X1=u1_struct_0(esk2_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_42, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.39  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  fof(c_0_44, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (v2_tex_2(u1_struct_0(esk2_2(esk3_0,esk4_0)),esk3_0)|v2_struct_0(esk2_2(esk3_0,esk4_0))|v1_xboole_0(esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_27])]), c_0_28]), c_0_40])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (u1_struct_0(esk2_2(esk3_0,esk4_0))=esk4_0|v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_27])]), c_0_28])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (~v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  fof(c_0_48, plain, ![X40, X41]:((~v2_tex_2(X41,X40)|v1_tdlat_3(X40)|X41!=u1_struct_0(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(v2_struct_0(X40)|~l1_pre_topc(X40)))&(~v1_tdlat_3(X40)|v2_tex_2(X41,X40)|X41!=u1_struct_0(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|(v2_struct_0(X40)|~l1_pre_topc(X40)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_tex_2])])])])])).
% 0.13/0.39  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.39  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.39  cnf(c_0_51, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk2_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (v2_struct_0(esk2_2(esk3_0,esk4_0))|v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.13/0.39  cnf(c_0_53, plain, (v2_tex_2(X2,X1)|v2_struct_0(X1)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.39  fof(c_0_54, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_55, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_27]), c_0_26])]), c_0_28])).
% 0.13/0.39  fof(c_0_57, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(X17))|k9_subset_1(X17,X18,X19)=k3_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.13/0.39  fof(c_0_58, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X14))|m1_subset_1(k9_subset_1(X14,X15,X16),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.13/0.39  fof(c_0_59, plain, ![X42, X43, X44]:((~v2_tex_2(X43,X42)|v2_tex_2(k9_subset_1(u1_struct_0(X42),X43,X44),X42)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X42))&(~v2_tex_2(X44,X42)|v2_tex_2(k9_subset_1(u1_struct_0(X42),X43,X44),X42)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42)))|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tex_2])])])])).
% 0.13/0.39  cnf(c_0_60, plain, (v2_tex_2(u1_struct_0(X1),X1)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_43])])).
% 0.13/0.39  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.39  cnf(c_0_63, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.39  fof(c_0_64, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  cnf(c_0_65, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.13/0.39  cnf(c_0_66, plain, (v2_tex_2(k9_subset_1(u1_struct_0(X2),X1,X3),X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (v2_tex_2(u1_struct_0(esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_35]), c_0_27])]), c_0_28])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (k3_xboole_0(X1,esk4_0)=k9_subset_1(u1_struct_0(esk3_0),X1,esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_26])).
% 0.13/0.39  cnf(c_0_70, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.39  cnf(c_0_71, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.39  cnf(c_0_72, plain, (m1_subset_1(k9_subset_1(X1,X2,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_65, c_0_43])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (v2_tex_2(k9_subset_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_27]), c_0_43])])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (k9_subset_1(X1,X2,esk4_0)=k9_subset_1(u1_struct_0(esk3_0),X2,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_68]), c_0_69])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (X1=esk4_0|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_70, c_0_62])).
% 0.13/0.39  cnf(c_0_76, plain, (r1_tarski(k9_subset_1(X1,X2,X1),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (v2_tex_2(k9_subset_1(X1,u1_struct_0(esk3_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_68])])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (k9_subset_1(esk4_0,X1,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_47]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 80
% 0.13/0.39  # Proof object clause steps            : 47
% 0.13/0.39  # Proof object formula steps           : 33
% 0.13/0.39  # Proof object conjectures             : 24
% 0.13/0.39  # Proof object clause conjectures      : 21
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 23
% 0.13/0.39  # Proof object initial formulas used   : 16
% 0.13/0.39  # Proof object generating inferences   : 20
% 0.13/0.39  # Proof object simplifying inferences  : 36
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 18
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 36
% 0.13/0.39  # Removed in clause preprocessing      : 1
% 0.13/0.39  # Initial clauses in saturation        : 35
% 0.13/0.39  # Processed clauses                    : 156
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 9
% 0.13/0.39  # ...remaining for further processing  : 145
% 0.13/0.39  # Other redundant clauses eliminated   : 6
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 7
% 0.13/0.39  # Backward-rewritten                   : 30
% 0.13/0.39  # Generated clauses                    : 248
% 0.13/0.39  # ...of the previous two non-trivial   : 199
% 0.13/0.39  # Contextual simplify-reflections      : 6
% 0.13/0.39  # Paramodulations                      : 242
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 6
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 68
% 0.13/0.39  #    Positive orientable unit clauses  : 24
% 0.13/0.39  #    Positive unorientable unit clauses: 1
% 0.13/0.39  #    Negative unit clauses             : 3
% 0.13/0.39  #    Non-unit-clauses                  : 40
% 0.13/0.39  # Current number of unprocessed clauses: 109
% 0.13/0.39  # ...number of literals in the above   : 270
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 72
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 996
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 287
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 16
% 0.13/0.39  # Unit Clause-clause subsumption calls : 84
% 0.13/0.39  # Rewrite failures with RHS unbound    : 10
% 0.13/0.39  # BW rewrite match attempts            : 74
% 0.13/0.39  # BW rewrite match successes           : 20
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 7420
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.043 s
% 0.13/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
