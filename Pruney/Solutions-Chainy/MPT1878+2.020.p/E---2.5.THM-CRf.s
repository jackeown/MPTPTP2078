%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:25 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 121 expanded)
%              Number of clauses        :   36 (  52 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  203 ( 408 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   31 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(rc1_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t46_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(c_0_15,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | m1_subset_1(X14,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X11] :
      ( ( m1_subset_1(esk2_1(X11),k1_zfmisc_1(X11))
        | v1_xboole_0(X11) )
      & ( ~ v1_xboole_0(esk2_1(X11))
        | v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ~ v3_tex_2(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t46_tex_2])).

fof(c_0_21,plain,(
    ! [X23,X24,X25] :
      ( ( v2_tex_2(X24,X23)
        | ~ v3_tex_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v2_tex_2(X25,X23)
        | ~ r1_tarski(X24,X25)
        | X24 = X25
        | ~ v3_tex_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk3_2(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ v2_tex_2(X24,X23)
        | v3_tex_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( v2_tex_2(esk3_2(X23,X24),X23)
        | ~ v2_tex_2(X24,X23)
        | v3_tex_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( r1_tarski(X24,esk3_2(X23,X24))
        | ~ v2_tex_2(X24,X23)
        | v3_tex_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( X24 != esk3_2(X23,X24)
        | ~ v2_tex_2(X24,X23)
        | v3_tex_2(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).

fof(c_0_22,plain,(
    ! [X13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_23,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_24,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X19)
      | ~ m1_subset_1(X20,X19)
      | m1_subset_1(k6_domain_1(X19,X20),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,esk2_1(X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & v3_tex_2(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_30,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tex_2(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_tex_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk1_1(esk2_1(X1)),X1)
    | v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

fof(c_0_35,plain,(
    ! [X27,X28] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | v2_tex_2(k6_domain_1(u1_struct_0(X27),X28),X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X21)
      | ~ m1_subset_1(X22,X21)
      | k6_domain_1(X21,X22) = k1_tarski(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ v2_tex_2(X1,X2)
    | ~ v3_tex_2(k1_xboole_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k6_domain_1(X1,esk1_1(esk2_1(X1))),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v3_tex_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_44,plain,(
    ! [X10] : ~ v1_xboole_0(k1_tarski(X10)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1)))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1)))),X1)
    | ~ v3_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1)))),X1)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( v3_tex_2(k1_xboole_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k1_tarski(esk1_1(esk2_1(X1))) = k6_domain_1(X1,esk1_1(esk2_1(X1)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_34])).

cnf(c_0_51,plain,
    ( k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1)))) = k1_xboole_0
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ v3_tex_2(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v3_tex_2(X1,esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_57,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(k6_domain_1(X1,esk1_1(esk2_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk2_1(u1_struct_0(esk4_0)))) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_54]),c_0_55])]),c_0_56])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_55])])).

fof(c_0_62,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_56])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 6.98/7.19  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S2q
% 6.98/7.19  # and selection function SelectCQArNTNp.
% 6.98/7.19  #
% 6.98/7.19  # Preprocessing time       : 0.028 s
% 6.98/7.19  # Presaturation interreduction done
% 6.98/7.19  
% 6.98/7.19  # Proof found!
% 6.98/7.19  # SZS status Theorem
% 6.98/7.19  # SZS output start CNFRefutation
% 6.98/7.19  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 6.98/7.19  fof(rc1_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 6.98/7.19  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.98/7.19  fof(t46_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 6.98/7.19  fof(d7_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tex_2(X2,X1)<=>(v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X3,X1)&r1_tarski(X2,X3))=>X2=X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 6.98/7.19  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.98/7.19  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.98/7.19  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 6.98/7.19  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.98/7.19  fof(t36_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 6.98/7.19  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.98/7.19  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.98/7.19  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.98/7.19  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.98/7.19  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.98/7.19  fof(c_0_15, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|m1_subset_1(X14,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 6.98/7.19  fof(c_0_16, plain, ![X11]:((m1_subset_1(esk2_1(X11),k1_zfmisc_1(X11))|v1_xboole_0(X11))&(~v1_xboole_0(esk2_1(X11))|v1_xboole_0(X11))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).
% 6.98/7.19  cnf(c_0_17, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 6.98/7.19  cnf(c_0_18, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.98/7.19  fof(c_0_19, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 6.98/7.19  fof(c_0_20, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1))))), inference(assume_negation,[status(cth)],[t46_tex_2])).
% 6.98/7.19  fof(c_0_21, plain, ![X23, X24, X25]:(((v2_tex_2(X24,X23)|~v3_tex_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~v2_tex_2(X25,X23)|~r1_tarski(X24,X25)|X24=X25)|~v3_tex_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&((m1_subset_1(esk3_2(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))|~v2_tex_2(X24,X23)|v3_tex_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(((v2_tex_2(esk3_2(X23,X24),X23)|~v2_tex_2(X24,X23)|v3_tex_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(r1_tarski(X24,esk3_2(X23,X24))|~v2_tex_2(X24,X23)|v3_tex_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&(X24!=esk3_2(X23,X24)|~v2_tex_2(X24,X23)|v3_tex_2(X24,X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_tex_2])])])])])).
% 6.98/7.19  fof(c_0_22, plain, ![X13]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 6.98/7.19  fof(c_0_23, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 6.98/7.19  fof(c_0_24, plain, ![X19, X20]:(v1_xboole_0(X19)|~m1_subset_1(X20,X19)|m1_subset_1(k6_domain_1(X19,X20),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 6.98/7.19  cnf(c_0_25, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,esk2_1(X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 6.98/7.19  cnf(c_0_26, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.98/7.19  cnf(c_0_27, plain, (v1_xboole_0(X1)|~v1_xboole_0(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.98/7.19  fof(c_0_28, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 6.98/7.19  fof(c_0_29, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&v3_tex_2(esk5_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 6.98/7.19  cnf(c_0_30, plain, (X3=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tex_2(X1,X2)|~r1_tarski(X3,X1)|~v3_tex_2(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.98/7.19  cnf(c_0_31, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.98/7.19  cnf(c_0_32, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.98/7.19  cnf(c_0_33, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 6.98/7.19  cnf(c_0_34, plain, (m1_subset_1(esk1_1(esk2_1(X1)),X1)|v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 6.98/7.19  fof(c_0_35, plain, ![X27, X28]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_subset_1(X28,u1_struct_0(X27))|v2_tex_2(k6_domain_1(u1_struct_0(X27),X28),X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).
% 6.98/7.19  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.98/7.19  cnf(c_0_37, negated_conjecture, (v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.98/7.19  fof(c_0_38, plain, ![X21, X22]:(v1_xboole_0(X21)|~m1_subset_1(X22,X21)|k6_domain_1(X21,X22)=k1_tarski(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 6.98/7.19  cnf(c_0_39, plain, (X1=k1_xboole_0|~v2_tex_2(X1,X2)|~v3_tex_2(k1_xboole_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 6.98/7.19  cnf(c_0_40, plain, (m1_subset_1(k6_domain_1(X1,esk1_1(esk2_1(X1))),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 6.98/7.19  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 6.98/7.19  cnf(c_0_42, negated_conjecture, (v3_tex_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.98/7.19  cnf(c_0_43, negated_conjecture, (esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 6.98/7.19  fof(c_0_44, plain, ![X10]:~v1_xboole_0(k1_tarski(X10)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 6.98/7.19  cnf(c_0_45, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.98/7.19  cnf(c_0_46, plain, (k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1))))=k1_xboole_0|v1_xboole_0(u1_struct_0(X1))|~v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1)))),X1)|~v3_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 6.98/7.19  cnf(c_0_47, plain, (v2_tex_2(k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1)))),X1)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 6.98/7.19  cnf(c_0_48, negated_conjecture, (v3_tex_2(k1_xboole_0,esk4_0)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 6.98/7.19  cnf(c_0_49, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 6.98/7.19  cnf(c_0_50, plain, (k1_tarski(esk1_1(esk2_1(X1)))=k6_domain_1(X1,esk1_1(esk2_1(X1)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_45, c_0_34])).
% 6.98/7.19  cnf(c_0_51, plain, (k6_domain_1(u1_struct_0(X1),esk1_1(esk2_1(u1_struct_0(X1))))=k1_xboole_0|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~v2_pre_topc(X1)|~v3_tex_2(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 6.98/7.19  cnf(c_0_52, negated_conjecture, (v3_tex_2(X1,esk4_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_36])).
% 6.98/7.19  cnf(c_0_53, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.98/7.19  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.98/7.19  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 6.98/7.19  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.98/7.19  fof(c_0_57, plain, ![X18]:(v2_struct_0(X18)|~l1_struct_0(X18)|~v1_xboole_0(u1_struct_0(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 6.98/7.19  cnf(c_0_58, plain, (v1_xboole_0(X1)|~v1_xboole_0(k6_domain_1(X1,esk1_1(esk2_1(X1))))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 6.98/7.19  cnf(c_0_59, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk1_1(esk2_1(u1_struct_0(esk4_0))))=k1_xboole_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_54]), c_0_55])]), c_0_56])).
% 6.98/7.19  cnf(c_0_60, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 6.98/7.19  cnf(c_0_61, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_55])])).
% 6.98/7.19  fof(c_0_62, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 6.98/7.19  cnf(c_0_63, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_56])).
% 6.98/7.19  cnf(c_0_64, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 6.98/7.19  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_54])]), ['proof']).
% 6.98/7.19  # SZS output end CNFRefutation
% 6.98/7.19  # Proof object total steps             : 66
% 6.98/7.19  # Proof object clause steps            : 36
% 6.98/7.19  # Proof object formula steps           : 30
% 6.98/7.19  # Proof object conjectures             : 15
% 6.98/7.19  # Proof object clause conjectures      : 12
% 6.98/7.19  # Proof object formula conjectures     : 3
% 6.98/7.19  # Proof object initial clauses used    : 20
% 6.98/7.19  # Proof object initial formulas used   : 15
% 6.98/7.19  # Proof object generating inferences   : 15
% 6.98/7.19  # Proof object simplifying inferences  : 14
% 6.98/7.19  # Training examples: 0 positive, 0 negative
% 6.98/7.19  # Parsed axioms                        : 15
% 6.98/7.19  # Removed by relevancy pruning/SinE    : 0
% 6.98/7.19  # Initial clauses                      : 27
% 6.98/7.19  # Removed in clause preprocessing      : 0
% 6.98/7.19  # Initial clauses in saturation        : 27
% 6.98/7.19  # Processed clauses                    : 17115
% 6.98/7.19  # ...of these trivial                  : 1
% 6.98/7.19  # ...subsumed                          : 14220
% 6.98/7.19  # ...remaining for further processing  : 2894
% 6.98/7.19  # Other redundant clauses eliminated   : 34
% 6.98/7.19  # Clauses deleted for lack of memory   : 0
% 6.98/7.19  # Backward-subsumed                    : 70
% 6.98/7.19  # Backward-rewritten                   : 4
% 6.98/7.19  # Generated clauses                    : 548281
% 6.98/7.19  # ...of the previous two non-trivial   : 518622
% 6.98/7.19  # Contextual simplify-reflections      : 57
% 6.98/7.19  # Paramodulations                      : 548177
% 6.98/7.19  # Factorizations                       : 70
% 6.98/7.19  # Equation resolutions                 : 34
% 6.98/7.19  # Propositional unsat checks           : 0
% 6.98/7.19  #    Propositional check models        : 0
% 6.98/7.19  #    Propositional check unsatisfiable : 0
% 6.98/7.19  #    Propositional clauses             : 0
% 6.98/7.19  #    Propositional clauses after purity: 0
% 6.98/7.19  #    Propositional unsat core size     : 0
% 6.98/7.19  #    Propositional preprocessing time  : 0.000
% 6.98/7.19  #    Propositional encoding time       : 0.000
% 6.98/7.19  #    Propositional solver time         : 0.000
% 6.98/7.19  #    Success case prop preproc time    : 0.000
% 6.98/7.19  #    Success case prop encoding time   : 0.000
% 6.98/7.19  #    Success case prop solver time     : 0.000
% 6.98/7.19  # Current number of processed clauses  : 2793
% 6.98/7.19  #    Positive orientable unit clauses  : 9
% 6.98/7.19  #    Positive unorientable unit clauses: 0
% 6.98/7.19  #    Negative unit clauses             : 3
% 6.98/7.19  #    Non-unit-clauses                  : 2781
% 6.98/7.19  # Current number of unprocessed clauses: 501236
% 6.98/7.19  # ...number of literals in the above   : 4003034
% 6.98/7.19  # Current number of archived formulas  : 0
% 6.98/7.19  # Current number of archived clauses   : 101
% 6.98/7.19  # Clause-clause subsumption calls (NU) : 1659904
% 6.98/7.19  # Rec. Clause-clause subsumption calls : 149142
% 6.98/7.19  # Non-unit clause-clause subsumptions  : 11888
% 6.98/7.19  # Unit Clause-clause subsumption calls : 2301
% 6.98/7.19  # Rewrite failures with RHS unbound    : 0
% 6.98/7.19  # BW rewrite match attempts            : 2
% 6.98/7.19  # BW rewrite match successes           : 2
% 6.98/7.19  # Condensation attempts                : 0
% 6.98/7.19  # Condensation successes               : 0
% 6.98/7.19  # Termbank termtop insertions          : 13824906
% 7.05/7.21  
% 7.05/7.21  # -------------------------------------------------
% 7.05/7.21  # User time                : 6.661 s
% 7.05/7.21  # System time              : 0.212 s
% 7.05/7.21  # Total time               : 6.874 s
% 7.05/7.21  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
