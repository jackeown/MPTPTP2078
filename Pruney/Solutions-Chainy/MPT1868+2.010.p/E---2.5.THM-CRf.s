%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 191 expanded)
%              Number of clauses        :   35 (  68 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  226 ( 847 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tex_2)).

fof(dt_k1_tex_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v2_struct_0(k1_tex_2(X1,X2))
        & v1_pre_topc(k1_tex_2(X1,X2))
        & m1_pre_topc(k1_tex_2(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(t36_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(t24_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v2_pre_topc(k1_tex_2(X1,X2))
           => ( v1_tdlat_3(k1_tex_2(X1,X2))
              & v2_tdlat_3(k1_tex_2(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,plain,(
    ! [X15,X16,X17] :
      ( ( X17 != k1_tex_2(X15,X16)
        | u1_struct_0(X17) = k6_domain_1(u1_struct_0(X15),X16)
        | v2_struct_0(X17)
        | ~ v1_pre_topc(X17)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) )
      & ( u1_struct_0(X17) != k6_domain_1(u1_struct_0(X15),X16)
        | X17 = k1_tex_2(X15,X16)
        | v2_struct_0(X17)
        | ~ v1_pre_topc(X17)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

fof(c_0_13,plain,(
    ! [X18,X19] :
      ( ( ~ v2_struct_0(k1_tex_2(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) )
      & ( v1_pre_topc(k1_tex_2(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) )
      & ( m1_pre_topc(k1_tex_2(X18,X19),X18)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

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
    ! [X13,X14] :
      ( v1_xboole_0(X13)
      | ~ m1_subset_1(X14,X13)
      | k6_domain_1(X13,X14) = k1_tarski(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_16,plain,(
    ! [X4] : k2_tarski(X4,X4) = k1_tarski(X4) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_17,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ v2_tex_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_22,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | m1_subset_1(k1_tarski(X5),k1_zfmisc_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = u1_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28])).

fof(c_0_32,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X7,X8)
      | v1_xboole_0(X8)
      | r2_hidden(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_33,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | v2_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_34,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v2_tex_2(X24,X22)
        | v1_tdlat_3(X23)
        | X24 != u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ v1_tdlat_3(X23)
        | v2_tex_2(X24,X22)
        | X24 != u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_29,c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( k2_tarski(esk2_0,esk2_0) = u1_struct_0(k1_tex_2(esk1_0,esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_31])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X20,X21] :
      ( ( v1_tdlat_3(k1_tex_2(X20,X21))
        | ~ v2_pre_topc(k1_tex_2(X20,X21))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20) )
      & ( v2_tdlat_3(k1_tex_2(X20,X21))
        | ~ v2_pre_topc(k1_tex_2(X20,X21))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tex_2])])])])])).

cnf(c_0_39,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk1_0,esk2_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_42,plain,(
    ! [X12] :
      ( v2_struct_0(X12)
      | ~ l1_struct_0(X12)
      | ~ v1_xboole_0(u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_43,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(X11)
      | l1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_44,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk2_0)),k1_zfmisc_1(X1))
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_47,plain,
    ( v1_tdlat_3(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(k1_tex_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v2_pre_topc(k1_tex_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_27]),c_0_41])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_tex_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( v1_tdlat_3(k1_tex_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_27]),c_0_26])]),c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_tex_2(u1_struct_0(k1_tex_2(esk1_0,esk2_0)),esk1_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_31])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_40]),c_0_27])]),c_0_55]),c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( v2_struct_0(k1_tex_2(esk1_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_27])]),c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_58]),c_0_27]),c_0_26])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:24:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 0.14/0.38  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.14/0.38  fof(t36_tex_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 0.14/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.14/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.38  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.14/0.38  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 0.14/0.38  fof(t24_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v2_pre_topc(k1_tex_2(X1,X2))=>(v1_tdlat_3(k1_tex_2(X1,X2))&v2_tdlat_3(k1_tex_2(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tex_2)).
% 0.14/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(c_0_12, plain, ![X15, X16, X17]:((X17!=k1_tex_2(X15,X16)|u1_struct_0(X17)=k6_domain_1(u1_struct_0(X15),X16)|(v2_struct_0(X17)|~v1_pre_topc(X17)|~m1_pre_topc(X17,X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l1_pre_topc(X15)))&(u1_struct_0(X17)!=k6_domain_1(u1_struct_0(X15),X16)|X17=k1_tex_2(X15,X16)|(v2_struct_0(X17)|~v1_pre_topc(X17)|~m1_pre_topc(X17,X15))|~m1_subset_1(X16,u1_struct_0(X15))|(v2_struct_0(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X18, X19]:(((~v2_struct_0(k1_tex_2(X18,X19))|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))&(v1_pre_topc(k1_tex_2(X18,X19))|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18)))))&(m1_pre_topc(k1_tex_2(X18,X19),X18)|(v2_struct_0(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.14/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)))), inference(assume_negation,[status(cth)],[t36_tex_2])).
% 0.14/0.38  fof(c_0_15, plain, ![X13, X14]:(v1_xboole_0(X13)|~m1_subset_1(X14,X13)|k6_domain_1(X13,X14)=k1_tarski(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.38  fof(c_0_16, plain, ![X4]:k2_tarski(X4,X4)=k1_tarski(X4), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  cnf(c_0_17, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X2),X3)|v2_struct_0(X1)|v2_struct_0(X2)|X1!=k1_tex_2(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_19, plain, (v1_pre_topc(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_20, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  fof(c_0_21, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&~v2_tex_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.14/0.38  fof(c_0_22, plain, ![X5, X6]:(~r2_hidden(X5,X6)|m1_subset_1(k1_tarski(X5),k1_zfmisc_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.14/0.38  cnf(c_0_23, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_25, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_18]), c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_29, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (k6_domain_1(u1_struct_0(esk1_0),esk2_0)=u1_struct_0(k1_tex_2(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_28])).
% 0.14/0.38  fof(c_0_32, plain, ![X7, X8]:(~m1_subset_1(X7,X8)|(v1_xboole_0(X8)|r2_hidden(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.38  fof(c_0_33, plain, ![X9, X10]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|v2_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.14/0.38  fof(c_0_34, plain, ![X22, X23, X24]:((~v2_tex_2(X24,X22)|v1_tdlat_3(X23)|X24!=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~l1_pre_topc(X22)))&(~v1_tdlat_3(X23)|v2_tex_2(X24,X22)|X24!=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X22))|(v2_struct_0(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.14/0.38  cnf(c_0_35, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_29, c_0_24])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (k2_tarski(esk2_0,esk2_0)=u1_struct_0(k1_tex_2(esk1_0,esk2_0))|v1_xboole_0(u1_struct_0(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_31])).
% 0.14/0.38  cnf(c_0_37, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  fof(c_0_38, plain, ![X20, X21]:((v1_tdlat_3(k1_tex_2(X20,X21))|~v2_pre_topc(k1_tex_2(X20,X21))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_pre_topc(X20)))&(v2_tdlat_3(k1_tex_2(X20,X21))|~v2_pre_topc(k1_tex_2(X20,X21))|~m1_subset_1(X21,u1_struct_0(X20))|(v2_struct_0(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_tex_2])])])])])).
% 0.14/0.38  cnf(c_0_39, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (m1_pre_topc(k1_tex_2(esk1_0,esk2_0),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_26]), c_0_27])]), c_0_28])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  fof(c_0_42, plain, ![X12]:(v2_struct_0(X12)|~l1_struct_0(X12)|~v1_xboole_0(u1_struct_0(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.38  fof(c_0_43, plain, ![X11]:(~l1_pre_topc(X11)|l1_struct_0(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  cnf(c_0_44, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk2_0)),k1_zfmisc_1(X1))|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_37, c_0_26])).
% 0.14/0.38  cnf(c_0_47, plain, (v1_tdlat_3(k1_tex_2(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(k1_tex_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (v2_pre_topc(k1_tex_2(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_27]), c_0_41])])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (~v2_tex_2(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_50, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_51, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.38  cnf(c_0_52, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_44])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(u1_struct_0(k1_tex_2(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (v1_tdlat_3(k1_tex_2(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_27]), c_0_26])]), c_0_28])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (~v2_tex_2(u1_struct_0(k1_tex_2(esk1_0,esk2_0)),esk1_0)), inference(rw,[status(thm)],[c_0_49, c_0_31])).
% 0.14/0.38  cnf(c_0_56, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (v2_struct_0(k1_tex_2(esk1_0,esk2_0))|v1_xboole_0(u1_struct_0(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_40]), c_0_27])]), c_0_55]), c_0_28])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (v2_struct_0(k1_tex_2(esk1_0,esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_27])]), c_0_28])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_58]), c_0_27]), c_0_26])]), c_0_28]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 60
% 0.14/0.38  # Proof object clause steps            : 35
% 0.14/0.38  # Proof object formula steps           : 25
% 0.14/0.38  # Proof object conjectures             : 20
% 0.14/0.38  # Proof object clause conjectures      : 17
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 18
% 0.14/0.38  # Proof object initial formulas used   : 12
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 35
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 12
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 21
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 20
% 0.14/0.38  # Processed clauses                    : 56
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 56
% 0.14/0.38  # Other redundant clauses eliminated   : 3
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 2
% 0.14/0.38  # Generated clauses                    : 22
% 0.14/0.38  # ...of the previous two non-trivial   : 21
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 19
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 3
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
% 0.14/0.38  # Current number of processed clauses  : 31
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 19
% 0.14/0.38  # Current number of unprocessed clauses: 5
% 0.14/0.38  # ...number of literals in the above   : 20
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 23
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 315
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 33
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.38  # Unit Clause-clause subsumption calls : 3
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2552
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.029 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
