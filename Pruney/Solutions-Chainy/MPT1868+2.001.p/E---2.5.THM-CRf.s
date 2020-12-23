%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:00 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 269 expanded)
%              Number of clauses        :   41 (  95 expanded)
%              Number of leaves         :   14 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  262 (1145 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(t30_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(t24_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v2_pre_topc(k1_tex_2(X1,X2))
           => ( v1_tdlat_3(k1_tex_2(X1,X2))
              & v2_tdlat_3(k1_tex_2(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t36_tex_2])).

fof(c_0_15,plain,(
    ! [X26,X27] :
      ( ( ~ v2_struct_0(k1_tex_2(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) )
      & ( v1_pre_topc(k1_tex_2(X26,X27))
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) )
      & ( m1_pre_topc(k1_tex_2(X26,X27),X26)
        | v2_struct_0(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,u1_struct_0(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & ~ v2_tex_2(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | m1_subset_1(k1_connsp_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | r2_hidden(X22,k1_connsp_2(X21,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).

fof(c_0_19,plain,(
    ! [X23,X24,X25] :
      ( ( X25 != k1_tex_2(X23,X24)
        | u1_struct_0(X25) = k6_domain_1(u1_struct_0(X23),X24)
        | v2_struct_0(X25)
        | ~ v1_pre_topc(X25)
        | ~ m1_pre_topc(X25,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) )
      & ( u1_struct_0(X25) != k6_domain_1(u1_struct_0(X23),X24)
        | X25 = k1_tex_2(X23,X24)
        | v2_struct_0(X25)
        | ~ v1_pre_topc(X25)
        | ~ m1_pre_topc(X25,X23)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | v2_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_21,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X17)
      | ~ m1_subset_1(X18,X17)
      | k6_domain_1(X17,X18) = k1_tarski(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_26,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_35,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v2_tex_2(X32,X30)
        | v1_tdlat_3(X31)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ v1_tdlat_3(X31)
        | v2_tex_2(X32,X30)
        | X32 != u1_struct_0(X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_36,plain,(
    ! [X28,X29] :
      ( ( v1_tdlat_3(k1_tex_2(X28,X29))
        | ~ v2_pre_topc(k1_tex_2(X28,X29))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28) )
      & ( v2_tdlat_3(k1_tex_2(X28,X29))
        | ~ v2_pre_topc(k1_tex_2(X28,X29))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tex_2])])])])])).

cnf(c_0_37,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23])]),c_0_24])).

cnf(c_0_43,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_0,k1_connsp_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_23]),c_0_29])]),c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_21]),c_0_33]),c_0_34])).

cnf(c_0_47,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( v1_tdlat_3(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(k1_tex_2(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23]),c_0_29])])).

cnf(c_0_50,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k1_connsp_2(esk2_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(k1_connsp_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_53,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_tex_2(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23]),c_0_22])]),c_0_24])).

cnf(c_0_55,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v1_tdlat_3(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_23]),c_0_22])]),c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(k1_tex_2(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_58,plain,
    ( u1_struct_0(k1_tex_2(X1,X2)) = k2_tarski(X2,X2)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_22]),c_0_52])).

fof(c_0_60,plain,(
    ! [X9,X10] :
      ( ~ r2_hidden(X9,X10)
      | m1_subset_1(k1_tarski(X9),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_38]),c_0_23])]),c_0_57]),c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk3_0)) = k2_tarski(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_23])]),c_0_24]),c_0_59])).

cnf(c_0_64,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_22])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_67,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_65,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:01:17 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.029 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t36_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 0.12/0.36  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.12/0.36  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.12/0.36  fof(t30_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_hidden(X2,k1_connsp_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 0.12/0.36  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 0.12/0.36  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.12/0.36  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.12/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.36  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.12/0.36  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.36  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 0.12/0.36  fof(t24_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v2_pre_topc(k1_tex_2(X1,X2))=>(v1_tdlat_3(k1_tex_2(X1,X2))&v2_tdlat_3(k1_tex_2(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tex_2)).
% 0.12/0.36  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.12/0.36  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.12/0.36  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)))), inference(assume_negation,[status(cth)],[t36_tex_2])).
% 0.12/0.36  fof(c_0_15, plain, ![X26, X27]:(((~v2_struct_0(k1_tex_2(X26,X27))|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))))&(v1_pre_topc(k1_tex_2(X26,X27))|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26)))))&(m1_pre_topc(k1_tex_2(X26,X27),X26)|(v2_struct_0(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.12/0.36  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&~v2_tex_2(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.12/0.36  fof(c_0_17, plain, ![X19, X20]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|~m1_subset_1(X20,u1_struct_0(X19))|m1_subset_1(k1_connsp_2(X19,X20),k1_zfmisc_1(u1_struct_0(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.12/0.36  fof(c_0_18, plain, ![X21, X22]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~m1_subset_1(X22,u1_struct_0(X21))|r2_hidden(X22,k1_connsp_2(X21,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).
% 0.12/0.36  fof(c_0_19, plain, ![X23, X24, X25]:((X25!=k1_tex_2(X23,X24)|u1_struct_0(X25)=k6_domain_1(u1_struct_0(X23),X24)|(v2_struct_0(X25)|~v1_pre_topc(X25)|~m1_pre_topc(X25,X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_pre_topc(X23)))&(u1_struct_0(X25)!=k6_domain_1(u1_struct_0(X23),X24)|X25=k1_tex_2(X23,X24)|(v2_struct_0(X25)|~v1_pre_topc(X25)|~m1_pre_topc(X25,X23))|~m1_subset_1(X24,u1_struct_0(X23))|(v2_struct_0(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 0.12/0.36  fof(c_0_20, plain, ![X15, X16]:(~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|v2_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.12/0.36  cnf(c_0_21, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  fof(c_0_25, plain, ![X17, X18]:(v1_xboole_0(X17)|~m1_subset_1(X18,X17)|k6_domain_1(X17,X18)=k1_tarski(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.12/0.36  fof(c_0_26, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.36  fof(c_0_27, plain, ![X11, X12]:(~v1_xboole_0(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.12/0.36  cnf(c_0_28, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  fof(c_0_30, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.36  cnf(c_0_31, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_connsp_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_32, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X2),X3)|v2_struct_0(X1)|v2_struct_0(X2)|X1!=k1_tex_2(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  cnf(c_0_33, plain, (v1_pre_topc(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_34, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  fof(c_0_35, plain, ![X30, X31, X32]:((~v2_tex_2(X32,X30)|v1_tdlat_3(X31)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X31)|~m1_pre_topc(X31,X30))|(v2_struct_0(X30)|~l1_pre_topc(X30)))&(~v1_tdlat_3(X31)|v2_tex_2(X32,X30)|X32!=u1_struct_0(X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X31)|~m1_pre_topc(X31,X30))|(v2_struct_0(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.12/0.36  fof(c_0_36, plain, ![X28, X29]:((v1_tdlat_3(k1_tex_2(X28,X29))|~v2_pre_topc(k1_tex_2(X28,X29))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~l1_pre_topc(X28)))&(v2_tdlat_3(k1_tex_2(X28,X29))|~v2_pre_topc(k1_tex_2(X28,X29))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tex_2])])])])])).
% 0.12/0.36  cnf(c_0_37, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_38, negated_conjecture, (m1_pre_topc(k1_tex_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])]), c_0_24])).
% 0.12/0.36  cnf(c_0_39, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.36  cnf(c_0_41, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, (m1_subset_1(k1_connsp_2(esk2_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23])]), c_0_24])).
% 0.12/0.36  cnf(c_0_43, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_0,k1_connsp_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_23]), c_0_29])]), c_0_24])).
% 0.12/0.36  cnf(c_0_45, negated_conjecture, (~v2_tex_2(k6_domain_1(u1_struct_0(esk2_0),esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_46, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_21]), c_0_33]), c_0_34])).
% 0.12/0.36  cnf(c_0_47, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.36  cnf(c_0_48, plain, (v1_tdlat_3(k1_tex_2(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.36  cnf(c_0_49, negated_conjecture, (v2_pre_topc(k1_tex_2(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23]), c_0_29])])).
% 0.12/0.36  cnf(c_0_50, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.36  cnf(c_0_51, negated_conjecture, (v1_xboole_0(k1_connsp_2(esk2_0,X1))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.36  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(k1_connsp_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.36  fof(c_0_53, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.12/0.36  cnf(c_0_54, negated_conjecture, (~v2_tex_2(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_23]), c_0_22])]), c_0_24])).
% 0.12/0.36  cnf(c_0_55, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_47])).
% 0.12/0.36  cnf(c_0_56, negated_conjecture, (v1_tdlat_3(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_23]), c_0_22])]), c_0_24])).
% 0.12/0.36  cnf(c_0_57, negated_conjecture, (~v2_struct_0(k1_tex_2(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_22]), c_0_23])]), c_0_24])).
% 0.12/0.36  cnf(c_0_58, plain, (u1_struct_0(k1_tex_2(X1,X2))=k2_tarski(X2,X2)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_46])).
% 0.12/0.36  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_22]), c_0_52])).
% 0.12/0.36  fof(c_0_60, plain, ![X9, X10]:(~r2_hidden(X9,X10)|m1_subset_1(k1_tarski(X9),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.12/0.36  cnf(c_0_61, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.12/0.36  cnf(c_0_62, negated_conjecture, (~m1_subset_1(u1_struct_0(k1_tex_2(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_38]), c_0_23])]), c_0_57]), c_0_24])).
% 0.12/0.36  cnf(c_0_63, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk3_0))=k2_tarski(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_22]), c_0_23])]), c_0_24]), c_0_59])).
% 0.12/0.36  cnf(c_0_64, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.36  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_0,u1_struct_0(esk2_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_61, c_0_22])).
% 0.12/0.36  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k2_tarski(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.12/0.36  cnf(c_0_67, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_40])).
% 0.12/0.36  cnf(c_0_68, negated_conjecture, (r2_hidden(esk3_0,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_65, c_0_59])).
% 0.12/0.36  cnf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 70
% 0.12/0.36  # Proof object clause steps            : 41
% 0.12/0.36  # Proof object formula steps           : 29
% 0.12/0.36  # Proof object conjectures             : 24
% 0.12/0.36  # Proof object clause conjectures      : 21
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 20
% 0.12/0.36  # Proof object initial formulas used   : 14
% 0.12/0.36  # Proof object generating inferences   : 15
% 0.12/0.36  # Proof object simplifying inferences  : 46
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 14
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 24
% 0.12/0.36  # Removed in clause preprocessing      : 1
% 0.12/0.36  # Initial clauses in saturation        : 23
% 0.12/0.36  # Processed clauses                    : 72
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 2
% 0.12/0.36  # ...remaining for further processing  : 70
% 0.12/0.36  # Other redundant clauses eliminated   : 3
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 2
% 0.12/0.36  # Generated clauses                    : 43
% 0.12/0.36  # ...of the previous two non-trivial   : 39
% 0.12/0.36  # Contextual simplify-reflections      : 3
% 0.12/0.36  # Paramodulations                      : 39
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 3
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 41
% 0.12/0.36  #    Positive orientable unit clauses  : 11
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 7
% 0.12/0.36  #    Non-unit-clauses                  : 23
% 0.12/0.36  # Current number of unprocessed clauses: 13
% 0.12/0.36  # ...number of literals in the above   : 61
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 27
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 151
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 15
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.36  # Unit Clause-clause subsumption calls : 12
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 3424
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.031 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.036 s
% 0.12/0.36  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
