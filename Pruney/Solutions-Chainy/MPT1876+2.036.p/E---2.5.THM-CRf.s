%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 531 expanded)
%              Number of clauses        :   67 ( 225 expanded)
%              Number of leaves         :   17 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  421 (2283 expanded)
%              Number of equality atoms :   19 (  81 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t44_tex_2,conjecture,(
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

fof(cc6_tdlat_3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_tdlat_3(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(cc2_tdlat_3,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_tdlat_3(X1)
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(cc2_tex_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v1_tdlat_3(X1)
          & v2_tdlat_3(X1) )
       => ( ~ v2_struct_0(X1)
          & v7_struct_0(X1)
          & v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

fof(t34_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & v1_tdlat_3(X3)
                    & m1_pre_topc(X3,X1) )
                 => X2 != u1_struct_0(X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_17,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ( ~ r1_tarski(k1_tarski(X15),X16)
        | r2_hidden(X15,X16) )
      & ( ~ r2_hidden(X15,X16)
        | r1_tarski(k1_tarski(X15),X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( v1_xboole_0(X31)
      | v1_xboole_0(X32)
      | ~ v1_zfmisc_1(X32)
      | ~ r1_tarski(X31,X32)
      | X31 = X32 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

fof(c_0_20,plain,(
    ! [X14] : ~ v1_xboole_0(k1_tarski(X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_21,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_tarski(X3))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( k1_tarski(X1) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_25]),c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_1(k1_tarski(X1)),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k1_tarski(esk1_1(k1_tarski(X1))) = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tex_2])).

cnf(c_0_38,plain,
    ( k1_tarski(esk1_1(k1_tarski(X1))) = k1_tarski(X1)
    | ~ v1_zfmisc_1(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,plain,
    ( k1_tarski(esk2_2(X1,X2)) = X1
    | r1_tarski(X1,X2)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

fof(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & v2_tdlat_3(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v2_tex_2(esk5_0,esk4_0)
      | ~ v1_zfmisc_1(esk5_0) )
    & ( v2_tex_2(esk5_0,esk4_0)
      | v1_zfmisc_1(esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).

cnf(c_0_41,plain,
    ( k1_tarski(esk1_1(X1)) = X1
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_42,plain,
    ( k1_tarski(esk1_1(X1)) = X1
    | r1_tarski(X1,X2)
    | ~ v1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_44,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ v2_tdlat_3(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | v2_tdlat_3(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).

fof(c_0_45,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | ~ v2_tdlat_3(X27)
      | v2_pre_topc(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_1(X1),X2)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k1_tarski(esk1_1(esk5_0)) = esk5_0
    | v2_tex_2(esk5_0,esk4_0)
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X28] :
      ( ( ~ v2_struct_0(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v1_tdlat_3(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) )
      & ( v7_struct_0(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v1_tdlat_3(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) )
      & ( v2_pre_topc(X28)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ v1_tdlat_3(X28)
        | ~ v2_tdlat_3(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_tdlat_3(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X33,X34] :
      ( ( ~ v2_struct_0(esk3_2(X33,X34))
        | ~ v2_tex_2(X34,X33)
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v1_pre_topc(esk3_2(X33,X34))
        | ~ v2_tex_2(X34,X33)
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v1_tdlat_3(esk3_2(X33,X34))
        | ~ v2_tex_2(X34,X33)
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_pre_topc(esk3_2(X33,X34),X33)
        | ~ v2_tex_2(X34,X33)
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( X34 = u1_struct_0(esk3_2(X33,X34))
        | ~ v2_tex_2(X34,X33)
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).

fof(c_0_53,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_54,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_1(k1_tarski(X1)),k1_tarski(X1))
    | ~ v1_zfmisc_1(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( k1_tarski(esk1_1(esk5_0)) = esk5_0
    | v2_tex_2(esk5_0,esk4_0)
    | r2_hidden(esk1_1(esk5_0),X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_43])).

fof(c_0_57,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_58,plain,
    ( v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(X2)
    | ~ v2_tdlat_3(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_60,plain,
    ( m1_pre_topc(esk3_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_61,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_62,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | v2_tex_2(k6_domain_1(u1_struct_0(X36),X37),X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | r2_hidden(esk1_1(esk5_0),esk5_0)
    | r2_hidden(esk1_1(esk5_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_43])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_58,c_0_51])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | v2_tdlat_3(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_51])).

cnf(c_0_70,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | r2_hidden(esk1_1(esk5_0),esk5_0) ),
    inference(ef,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_75,plain,(
    ! [X24] :
      ( ~ v7_struct_0(X24)
      | ~ l1_struct_0(X24)
      | v1_zfmisc_1(u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk3_2(X1,X2))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_77,plain,
    ( v2_struct_0(esk3_2(X1,X2))
    | v2_struct_0(X1)
    | v7_struct_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk3_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(esk3_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | l1_pre_topc(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_60])).

fof(c_0_79,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_80,plain,
    ( v2_tex_2(k1_tarski(X1),X2)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( k1_tarski(esk1_1(esk5_0)) = esk5_0
    | v2_tex_2(esk5_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_73]),c_0_43])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_74])).

cnf(c_0_83,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( X1 = u1_struct_0(esk3_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_85,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v1_tdlat_3(esk3_2(X1,X2))
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),c_0_51])).

cnf(c_0_86,plain,
    ( v1_tdlat_3(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_87,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0)
    | v2_tex_2(esk5_0,X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(esk1_1(esk5_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_28]),c_0_48])).

cnf(c_0_90,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_91,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_93,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v7_struct_0(esk3_2(X1,X2))
    | ~ l1_struct_0(esk3_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_94,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_51])).

cnf(c_0_95,plain,
    ( v2_struct_0(X1)
    | l1_struct_0(esk3_2(X1,X2))
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_78])).

cnf(c_0_96,negated_conjecture,
    ( ~ v2_tex_2(esk5_0,esk4_0)
    | ~ v1_zfmisc_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_97,negated_conjecture,
    ( v2_tex_2(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90]),c_0_91])]),c_0_92])).

cnf(c_0_98,plain,
    ( v2_struct_0(X1)
    | v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ v2_tex_2(X2,X1)
    | ~ v2_tdlat_3(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_51])).

cnf(c_0_99,negated_conjecture,
    ( v2_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_zfmisc_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_97]),c_0_99]),c_0_91]),c_0_67])]),c_0_92]),c_0_100]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.48  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.21/0.48  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.48  #
% 0.21/0.48  # Preprocessing time       : 0.029 s
% 0.21/0.48  # Presaturation interreduction done
% 0.21/0.48  
% 0.21/0.48  # Proof found!
% 0.21/0.48  # SZS status Theorem
% 0.21/0.48  # SZS output start CNFRefutation
% 0.21/0.48  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.48  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.21/0.48  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 0.21/0.48  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.21/0.48  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.48  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.21/0.48  fof(cc6_tdlat_3, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_tdlat_3(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 0.21/0.48  fof(cc2_tdlat_3, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_tdlat_3(X1)=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 0.21/0.48  fof(cc2_tex_1, axiom, ![X1]:(l1_pre_topc(X1)=>((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v1_tdlat_3(X1))&v2_tdlat_3(X1))=>((~(v2_struct_0(X1))&v7_struct_0(X1))&v2_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 0.21/0.48  fof(t34_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v2_tex_2(X2,X1)&![X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&v1_tdlat_3(X3))&m1_pre_topc(X3,X1))=>X2!=u1_struct_0(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 0.21/0.48  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.21/0.48  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.21/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.48  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.48  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.21/0.48  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.21/0.48  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.48  fof(c_0_17, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk2_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk2_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.48  fof(c_0_18, plain, ![X15, X16]:((~r1_tarski(k1_tarski(X15),X16)|r2_hidden(X15,X16))&(~r2_hidden(X15,X16)|r1_tarski(k1_tarski(X15),X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.21/0.48  fof(c_0_19, plain, ![X31, X32]:(v1_xboole_0(X31)|(v1_xboole_0(X32)|~v1_zfmisc_1(X32)|(~r1_tarski(X31,X32)|X31=X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 0.21/0.48  fof(c_0_20, plain, ![X14]:~v1_xboole_0(k1_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.21/0.48  fof(c_0_21, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.48  cnf(c_0_22, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.48  cnf(c_0_23, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.48  cnf(c_0_24, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.48  cnf(c_0_25, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.48  cnf(c_0_26, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.48  cnf(c_0_27, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_tarski(X3))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.48  cnf(c_0_28, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.48  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.48  cnf(c_0_30, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.48  cnf(c_0_31, plain, (k1_tarski(X1)=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_25]), c_0_26])).
% 0.21/0.48  cnf(c_0_32, plain, (r2_hidden(esk1_1(k1_tarski(X1)),X2)|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_25])).
% 0.21/0.48  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.48  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.48  cnf(c_0_35, plain, (k1_tarski(esk1_1(k1_tarski(X1)))=X2|~v1_zfmisc_1(X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.48  cnf(c_0_36, plain, (r2_hidden(X1,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.48  fof(c_0_37, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.21/0.48  cnf(c_0_38, plain, (k1_tarski(esk1_1(k1_tarski(X1)))=k1_tarski(X1)|~v1_zfmisc_1(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.48  cnf(c_0_39, plain, (k1_tarski(esk2_2(X1,X2))=X1|r1_tarski(X1,X2)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.21/0.48  fof(c_0_40, negated_conjecture, ((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v2_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0))&(v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])).
% 0.21/0.48  cnf(c_0_41, plain, (k1_tarski(esk1_1(X1))=X1|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 0.21/0.48  cnf(c_0_42, plain, (k1_tarski(esk1_1(X1))=X1|r1_tarski(X1,X2)|~v1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.48  cnf(c_0_43, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  fof(c_0_44, plain, ![X29, X30]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~v2_tdlat_3(X29)|~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|v2_tdlat_3(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_tdlat_3])])])])).
% 0.21/0.48  fof(c_0_45, plain, ![X27]:(~l1_pre_topc(X27)|(~v2_tdlat_3(X27)|v2_pre_topc(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_tdlat_3])])).
% 0.21/0.48  cnf(c_0_46, plain, (r2_hidden(esk1_1(X1),X2)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_41])).
% 0.21/0.48  cnf(c_0_47, negated_conjecture, (k1_tarski(esk1_1(esk5_0))=esk5_0|v2_tex_2(esk5_0,esk4_0)|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.48  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  fof(c_0_49, plain, ![X28]:(((~v2_struct_0(X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v1_tdlat_3(X28)|~v2_tdlat_3(X28))|~l1_pre_topc(X28))&(v7_struct_0(X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v1_tdlat_3(X28)|~v2_tdlat_3(X28))|~l1_pre_topc(X28)))&(v2_pre_topc(X28)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~v1_tdlat_3(X28)|~v2_tdlat_3(X28))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_tex_1])])])])).
% 0.21/0.48  cnf(c_0_50, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_pre_topc(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.48  cnf(c_0_51, plain, (v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_tdlat_3(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.48  fof(c_0_52, plain, ![X33, X34]:(((((~v2_struct_0(esk3_2(X33,X34))|~v2_tex_2(X34,X33)|(v1_xboole_0(X34)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(v1_pre_topc(esk3_2(X33,X34))|~v2_tex_2(X34,X33)|(v1_xboole_0(X34)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(v1_tdlat_3(esk3_2(X33,X34))|~v2_tex_2(X34,X33)|(v1_xboole_0(X34)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(m1_pre_topc(esk3_2(X33,X34),X33)|~v2_tex_2(X34,X33)|(v1_xboole_0(X34)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(X34=u1_struct_0(esk3_2(X33,X34))|~v2_tex_2(X34,X33)|(v1_xboole_0(X34)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_tex_2])])])])])])).
% 0.21/0.48  fof(c_0_53, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|k6_domain_1(X25,X26)=k1_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.21/0.48  fof(c_0_54, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.21/0.48  cnf(c_0_55, plain, (r2_hidden(esk1_1(k1_tarski(X1)),k1_tarski(X1))|~v1_zfmisc_1(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_36, c_0_38])).
% 0.21/0.48  cnf(c_0_56, negated_conjecture, (k1_tarski(esk1_1(esk5_0))=esk5_0|v2_tex_2(esk5_0,esk4_0)|r2_hidden(esk1_1(esk5_0),X1)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_43])).
% 0.21/0.48  fof(c_0_57, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.48  cnf(c_0_58, plain, (v7_struct_0(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.48  cnf(c_0_59, plain, (v2_struct_0(X1)|v2_tdlat_3(X2)|~v2_tdlat_3(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.48  cnf(c_0_60, plain, (m1_pre_topc(esk3_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.48  fof(c_0_61, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.48  fof(c_0_62, plain, ![X36, X37]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_subset_1(X37,u1_struct_0(X36))|v2_tex_2(k6_domain_1(u1_struct_0(X36),X37),X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 0.21/0.48  cnf(c_0_63, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.21/0.48  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.48  cnf(c_0_65, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|r2_hidden(esk1_1(esk5_0),esk5_0)|r2_hidden(esk1_1(esk5_0),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_43])).
% 0.21/0.48  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.48  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  cnf(c_0_68, plain, (v2_struct_0(X1)|v7_struct_0(X1)|~v1_tdlat_3(X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_58, c_0_51])).
% 0.21/0.48  cnf(c_0_69, plain, (v2_struct_0(X1)|v2_tdlat_3(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_51])).
% 0.21/0.48  cnf(c_0_70, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.48  cnf(c_0_71, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.48  cnf(c_0_72, plain, (k6_domain_1(X1,X2)=k1_tarski(X2)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_26])).
% 0.21/0.48  cnf(c_0_73, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|r2_hidden(esk1_1(esk5_0),esk5_0)), inference(ef,[status(thm)],[c_0_65])).
% 0.21/0.48  cnf(c_0_74, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.48  fof(c_0_75, plain, ![X24]:(~v7_struct_0(X24)|~l1_struct_0(X24)|v1_zfmisc_1(u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.21/0.48  cnf(c_0_76, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk3_2(X1,X2))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.48  cnf(c_0_77, plain, (v2_struct_0(esk3_2(X1,X2))|v2_struct_0(X1)|v7_struct_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk3_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(esk3_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.48  cnf(c_0_78, plain, (v2_struct_0(X1)|l1_pre_topc(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_70, c_0_60])).
% 0.21/0.48  fof(c_0_79, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.48  cnf(c_0_80, plain, (v2_tex_2(k1_tarski(X1),X2)|v2_struct_0(X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_64])).
% 0.21/0.48  cnf(c_0_81, negated_conjecture, (k1_tarski(esk1_1(esk5_0))=esk5_0|v2_tex_2(esk5_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_73]), c_0_43])).
% 0.21/0.48  cnf(c_0_82, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_74])).
% 0.21/0.48  cnf(c_0_83, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.48  cnf(c_0_84, plain, (X1=u1_struct_0(esk3_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.48  cnf(c_0_85, plain, (v2_struct_0(X1)|v7_struct_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v1_tdlat_3(esk3_2(X1,X2))|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), c_0_51])).
% 0.21/0.48  cnf(c_0_86, plain, (v1_tdlat_3(esk3_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.48  cnf(c_0_87, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.48  cnf(c_0_88, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)|v2_tex_2(esk5_0,X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(esk1_1(esk5_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.21/0.48  cnf(c_0_89, negated_conjecture, (r2_hidden(esk1_1(esk5_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_28]), c_0_48])).
% 0.21/0.48  cnf(c_0_90, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  cnf(c_0_91, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  cnf(c_0_92, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  cnf(c_0_93, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~v7_struct_0(esk3_2(X1,X2))|~l1_struct_0(esk3_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.21/0.48  cnf(c_0_94, plain, (v2_struct_0(X1)|v7_struct_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_51])).
% 0.21/0.48  cnf(c_0_95, plain, (v2_struct_0(X1)|l1_struct_0(esk3_2(X1,X2))|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_87, c_0_78])).
% 0.21/0.48  cnf(c_0_96, negated_conjecture, (~v2_tex_2(esk5_0,esk4_0)|~v1_zfmisc_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  cnf(c_0_97, negated_conjecture, (v2_tex_2(esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_90]), c_0_91])]), c_0_92])).
% 0.21/0.48  cnf(c_0_98, plain, (v2_struct_0(X1)|v1_zfmisc_1(X2)|v1_xboole_0(X2)|~v2_tex_2(X2,X1)|~v2_tdlat_3(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_51])).
% 0.21/0.48  cnf(c_0_99, negated_conjecture, (v2_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.48  cnf(c_0_100, negated_conjecture, (~v1_zfmisc_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])])).
% 0.21/0.48  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_97]), c_0_99]), c_0_91]), c_0_67])]), c_0_92]), c_0_100]), c_0_48]), ['proof']).
% 0.21/0.48  # SZS output end CNFRefutation
% 0.21/0.48  # Proof object total steps             : 102
% 0.21/0.48  # Proof object clause steps            : 67
% 0.21/0.48  # Proof object formula steps           : 35
% 0.21/0.48  # Proof object conjectures             : 23
% 0.21/0.48  # Proof object clause conjectures      : 20
% 0.21/0.48  # Proof object formula conjectures     : 3
% 0.21/0.48  # Proof object initial clauses used    : 31
% 0.21/0.48  # Proof object initial formulas used   : 17
% 0.21/0.48  # Proof object generating inferences   : 33
% 0.21/0.48  # Proof object simplifying inferences  : 31
% 0.21/0.48  # Training examples: 0 positive, 0 negative
% 0.21/0.48  # Parsed axioms                        : 17
% 0.21/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.48  # Initial clauses                      : 35
% 0.21/0.48  # Removed in clause preprocessing      : 2
% 0.21/0.48  # Initial clauses in saturation        : 33
% 0.21/0.48  # Processed clauses                    : 1447
% 0.21/0.48  # ...of these trivial                  : 4
% 0.21/0.48  # ...subsumed                          : 1069
% 0.21/0.48  # ...remaining for further processing  : 374
% 0.21/0.48  # Other redundant clauses eliminated   : 0
% 0.21/0.48  # Clauses deleted for lack of memory   : 0
% 0.21/0.48  # Backward-subsumed                    : 27
% 0.21/0.48  # Backward-rewritten                   : 15
% 0.21/0.48  # Generated clauses                    : 3963
% 0.21/0.48  # ...of the previous two non-trivial   : 3585
% 0.21/0.48  # Contextual simplify-reflections      : 33
% 0.21/0.48  # Paramodulations                      : 3961
% 0.21/0.48  # Factorizations                       : 2
% 0.21/0.48  # Equation resolutions                 : 0
% 0.21/0.48  # Propositional unsat checks           : 0
% 0.21/0.48  #    Propositional check models        : 0
% 0.21/0.48  #    Propositional check unsatisfiable : 0
% 0.21/0.48  #    Propositional clauses             : 0
% 0.21/0.48  #    Propositional clauses after purity: 0
% 0.21/0.48  #    Propositional unsat core size     : 0
% 0.21/0.48  #    Propositional preprocessing time  : 0.000
% 0.21/0.48  #    Propositional encoding time       : 0.000
% 0.21/0.48  #    Propositional solver time         : 0.000
% 0.21/0.48  #    Success case prop preproc time    : 0.000
% 0.21/0.48  #    Success case prop encoding time   : 0.000
% 0.21/0.48  #    Success case prop solver time     : 0.000
% 0.21/0.48  # Current number of processed clauses  : 299
% 0.21/0.48  #    Positive orientable unit clauses  : 14
% 0.21/0.48  #    Positive unorientable unit clauses: 0
% 0.21/0.48  #    Negative unit clauses             : 7
% 0.21/0.48  #    Non-unit-clauses                  : 278
% 0.21/0.48  # Current number of unprocessed clauses: 2064
% 0.21/0.48  # ...number of literals in the above   : 9509
% 0.21/0.48  # Current number of archived formulas  : 0
% 0.21/0.48  # Current number of archived clauses   : 75
% 0.21/0.48  # Clause-clause subsumption calls (NU) : 28794
% 0.21/0.48  # Rec. Clause-clause subsumption calls : 11102
% 0.21/0.48  # Non-unit clause-clause subsumptions  : 600
% 0.21/0.48  # Unit Clause-clause subsumption calls : 224
% 0.21/0.48  # Rewrite failures with RHS unbound    : 0
% 0.21/0.48  # BW rewrite match attempts            : 20
% 0.21/0.48  # BW rewrite match successes           : 3
% 0.21/0.48  # Condensation attempts                : 0
% 0.21/0.48  # Condensation successes               : 0
% 0.21/0.48  # Termbank termtop insertions          : 76171
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.139 s
% 0.21/0.49  # System time              : 0.002 s
% 0.21/0.49  # Total time               : 0.142 s
% 0.21/0.49  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
