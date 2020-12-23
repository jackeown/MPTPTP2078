%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 (3891 expanded)
%              Number of clauses        :   78 (1497 expanded)
%              Number of leaves         :   16 ( 964 expanded)
%              Depth                    :   14
%              Number of atoms          :  322 (15973 expanded)
%              Number of equality atoms :   49 (1674 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v7_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tex_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(d1_tex_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ( v7_struct_0(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
            & u1_struct_0(X1) = k6_domain_1(u1_struct_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

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

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v7_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tex_2])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_18,negated_conjecture,(
    ! [X34] :
      ( ~ v2_struct_0(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v7_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ( ~ m1_subset_1(X34,u1_struct_0(esk2_0))
        | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk2_0,X34)),u1_pre_topc(k1_tex_2(esk2_0,X34))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

fof(c_0_19,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | m1_pre_topc(X21,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X19,X20] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)),X19)
        | ~ m1_pre_topc(X20,X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_24,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ( ~ m1_pre_topc(X15,X16)
        | m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))
        | m1_pre_topc(X15,X16)
        | ~ l1_pre_topc(X16)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

fof(c_0_27,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_28,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | r1_tarski(u1_struct_0(X23),u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_29,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X13,X12)
      | ~ m1_subset_1(X14,u1_struct_0(X13))
      | m1_subset_1(X14,u1_struct_0(X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_33,plain,(
    ! [X24,X26] :
      ( ( m1_subset_1(esk1_1(X24),u1_struct_0(X24))
        | ~ v7_struct_0(X24)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24) )
      & ( u1_struct_0(X24) = k6_domain_1(u1_struct_0(X24),esk1_1(X24))
        | ~ v7_struct_0(X24)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X24))
        | u1_struct_0(X24) != k6_domain_1(u1_struct_0(X24),X26)
        | v7_struct_0(X24)
        | v2_struct_0(X24)
        | ~ l1_struct_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_1])])])])])])).

cnf(c_0_34,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X17,X18] :
      ( v1_xboole_0(X17)
      | ~ m1_subset_1(X18,X17)
      | k6_domain_1(X17,X18) = k1_tarski(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_36,plain,(
    ! [X6] : k2_tarski(X6,X6) = k1_tarski(X6) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_37,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ l1_struct_0(X11)
      | ~ v1_xboole_0(u1_struct_0(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_38,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_25])])).

cnf(c_0_41,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk1_1(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_47,negated_conjecture,
    ( v7_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X1),esk1_1(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_25])])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_25])])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_40]),c_0_25])])).

fof(c_0_56,plain,(
    ! [X10] :
      ( ~ v2_struct_0(X10)
      | ~ l1_struct_0(X10)
      | v1_xboole_0(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_57,plain,(
    ! [X27,X28,X29] :
      ( ( X29 != k1_tex_2(X27,X28)
        | u1_struct_0(X29) = k6_domain_1(u1_struct_0(X27),X28)
        | v2_struct_0(X29)
        | ~ v1_pre_topc(X29)
        | ~ m1_pre_topc(X29,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27) )
      & ( u1_struct_0(X29) != k6_domain_1(u1_struct_0(X27),X28)
        | X29 = k1_tex_2(X27,X28)
        | v2_struct_0(X29)
        | ~ v1_pre_topc(X29)
        | ~ m1_pre_topc(X29,X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).

fof(c_0_58,plain,(
    ! [X30,X31] :
      ( ( ~ v2_struct_0(k1_tex_2(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30)) )
      & ( v1_pre_topc(k1_tex_2(X30,X31))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30)) )
      & ( m1_pre_topc(k1_tex_2(X30,X31),X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | ~ m1_subset_1(X31,u1_struct_0(X30)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_22])]),c_0_43]),c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_43])).

cnf(c_0_61,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_46]),c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk3_0),esk1_1(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_47])]),c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_65,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_25])])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk3_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_54]),c_0_55])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_55])).

cnf(c_0_70,plain,
    ( u1_struct_0(X1) = k6_domain_1(u1_struct_0(X2),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | X1 != k1_tex_2(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_71,plain,
    ( m1_pre_topc(k1_tex_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,plain,
    ( v1_pre_topc(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_1(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( k2_tarski(esk1_1(esk3_0),esk1_1(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_60]),c_0_62]),c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_64]),c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_65]),c_0_25])])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_79,negated_conjecture,
    ( m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_54]),c_0_55])])).

cnf(c_0_80,plain,
    ( X1 = k1_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | u1_struct_0(X1) != k6_domain_1(u1_struct_0(X2),X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_81,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_83,plain,
    ( k6_domain_1(u1_struct_0(X1),X2) = u1_struct_0(k1_tex_2(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_71]),c_0_72]),c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk1_1(esk3_0)) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))),esk3_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( X1 = k1_tex_2(esk3_0,esk1_1(esk3_0))
    | v2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(esk3_0)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_63]),c_0_60]),c_0_25])]),c_0_43])).

cnf(c_0_89,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_30]),c_0_25])])).

cnf(c_0_90,negated_conjecture,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_78]),c_0_62])).

cnf(c_0_91,negated_conjecture,
    ( m1_pre_topc(k1_tex_2(esk3_0,esk1_1(esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_60]),c_0_25])]),c_0_43])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk3_0,esk1_1(esk3_0))) = u1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_60]),c_0_63]),c_0_25])]),c_0_43])).

cnf(c_0_93,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) != g1_pre_topc(u1_struct_0(k1_tex_2(esk2_0,X1)),u1_pre_topc(k1_tex_2(esk2_0,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(k1_tex_2(esk2_0,esk1_1(esk3_0))) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_74]),c_0_22])]),c_0_44]),c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( X1 = k1_tex_2(esk2_0,esk1_1(esk3_0))
    | v2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(esk3_0)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_84]),c_0_74]),c_0_22])]),c_0_44])).

cnf(c_0_96,negated_conjecture,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_22])])).

cnf(c_0_97,negated_conjecture,
    ( l1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_86]),c_0_25])])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_87]),c_0_85])])).

cnf(c_0_100,negated_conjecture,
    ( k1_tex_2(esk3_0,esk1_1(esk3_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_78]),c_0_89]),c_0_40])]),c_0_90])).

cnf(c_0_101,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k1_tex_2(esk3_0,esk1_1(esk3_0))))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_91]),c_0_25])]),c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k1_tex_2(esk2_0,esk1_1(esk3_0)))) != g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_74])])).

cnf(c_0_103,negated_conjecture,
    ( k1_tex_2(esk2_0,esk1_1(esk3_0)) = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_78]),c_0_89]),c_0_96])]),c_0_90])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))
    | ~ v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_98]),c_0_99])])).

cnf(c_0_106,negated_conjecture,
    ( X1 = g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))
    | v2_struct_0(X1)
    | u1_struct_0(X1) != u1_struct_0(esk3_0)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(rw,[status(thm)],[c_0_101,c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) != g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105]),c_0_62])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_105]),c_0_107]),c_0_86])]),c_0_108]),c_0_109]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:20:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.19/0.39  # and selection function SelectGrCQArEqFirst.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t23_tex_2, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v7_struct_0(X2))&m1_pre_topc(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tex_2)).
% 0.19/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.39  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.19/0.39  fof(t11_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))&m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 0.19/0.39  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.39  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.19/0.39  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.19/0.39  fof(d1_tex_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>(v7_struct_0(X1)<=>?[X2]:(m1_subset_1(X2,u1_struct_0(X1))&u1_struct_0(X1)=k6_domain_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_1)).
% 0.19/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.39  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.19/0.39  fof(d4_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>(X3=k1_tex_2(X1,X2)<=>u1_struct_0(X3)=k6_domain_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tex_2)).
% 0.19/0.39  fof(dt_k1_tex_2, axiom, ![X1, X2]:(((~(v2_struct_0(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>((~(v2_struct_0(k1_tex_2(X1,X2)))&v1_pre_topc(k1_tex_2(X1,X2)))&m1_pre_topc(k1_tex_2(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 0.19/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v7_struct_0(X2))&m1_pre_topc(X2,X1))=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(k1_tex_2(X1,X3)),u1_pre_topc(k1_tex_2(X1,X3))))))), inference(assume_negation,[status(cth)],[t23_tex_2])).
% 0.19/0.39  fof(c_0_17, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.39  fof(c_0_18, negated_conjecture, ![X34]:((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v7_struct_0(esk3_0))&m1_pre_topc(esk3_0,esk2_0))&(~m1_subset_1(X34,u1_struct_0(esk2_0))|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(u1_struct_0(k1_tex_2(esk2_0,X34)),u1_pre_topc(k1_tex_2(esk2_0,X34)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.19/0.39  fof(c_0_19, plain, ![X21]:(~l1_pre_topc(X21)|m1_pre_topc(X21,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.19/0.39  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_23, plain, ![X19, X20]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)))|~m1_pre_topc(X20,X19)|~l1_pre_topc(X19))&(m1_pre_topc(g1_pre_topc(u1_struct_0(X20),u1_pre_topc(X20)),X19)|~m1_pre_topc(X20,X19)|~l1_pre_topc(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).
% 0.19/0.39  cnf(c_0_24, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.19/0.39  fof(c_0_26, plain, ![X15, X16]:((~m1_pre_topc(X15,X16)|m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|~l1_pre_topc(X16)|~l1_pre_topc(X15))&(~m1_pre_topc(X15,g1_pre_topc(u1_struct_0(X16),u1_pre_topc(X16)))|m1_pre_topc(X15,X16)|~l1_pre_topc(X16)|~l1_pre_topc(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.39  fof(c_0_27, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.39  fof(c_0_28, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|r1_tarski(u1_struct_0(X23),u1_struct_0(X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.19/0.39  cnf(c_0_29, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.39  cnf(c_0_31, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  fof(c_0_32, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~l1_pre_topc(X12)|(v2_struct_0(X13)|~m1_pre_topc(X13,X12)|(~m1_subset_1(X14,u1_struct_0(X13))|m1_subset_1(X14,u1_struct_0(X12))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.19/0.39  fof(c_0_33, plain, ![X24, X26]:(((m1_subset_1(esk1_1(X24),u1_struct_0(X24))|~v7_struct_0(X24)|(v2_struct_0(X24)|~l1_struct_0(X24)))&(u1_struct_0(X24)=k6_domain_1(u1_struct_0(X24),esk1_1(X24))|~v7_struct_0(X24)|(v2_struct_0(X24)|~l1_struct_0(X24))))&(~m1_subset_1(X26,u1_struct_0(X24))|u1_struct_0(X24)!=k6_domain_1(u1_struct_0(X24),X26)|v7_struct_0(X24)|(v2_struct_0(X24)|~l1_struct_0(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_1])])])])])])).
% 0.19/0.39  cnf(c_0_34, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  fof(c_0_35, plain, ![X17, X18]:(v1_xboole_0(X17)|~m1_subset_1(X18,X17)|k6_domain_1(X17,X18)=k1_tarski(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.39  fof(c_0_36, plain, ![X6]:k2_tarski(X6,X6)=k1_tarski(X6), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_37, plain, ![X11]:(v2_struct_0(X11)|~l1_struct_0(X11)|~v1_xboole_0(u1_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.39  fof(c_0_38, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.39  cnf(c_0_39, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_25])])).
% 0.19/0.39  cnf(c_0_41, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_31, c_0_20])).
% 0.19/0.39  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_45, plain, (m1_subset_1(esk1_1(X1),u1_struct_0(X1))|v2_struct_0(X1)|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (v7_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_48, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_49, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_51, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X1),esk1_1(X1))|v2_struct_0(X1)|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_25])])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_25])])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_40]), c_0_25])])).
% 0.19/0.39  fof(c_0_56, plain, ![X10]:(~v2_struct_0(X10)|~l1_struct_0(X10)|v1_xboole_0(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.19/0.39  fof(c_0_57, plain, ![X27, X28, X29]:((X29!=k1_tex_2(X27,X28)|u1_struct_0(X29)=k6_domain_1(u1_struct_0(X27),X28)|(v2_struct_0(X29)|~v1_pre_topc(X29)|~m1_pre_topc(X29,X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~l1_pre_topc(X27)))&(u1_struct_0(X29)!=k6_domain_1(u1_struct_0(X27),X28)|X29=k1_tex_2(X27,X28)|(v2_struct_0(X29)|~v1_pre_topc(X29)|~m1_pre_topc(X29,X27))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tex_2])])])])])).
% 0.19/0.39  fof(c_0_58, plain, ![X30, X31]:(((~v2_struct_0(k1_tex_2(X30,X31))|(v2_struct_0(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,u1_struct_0(X30))))&(v1_pre_topc(k1_tex_2(X30,X31))|(v2_struct_0(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,u1_struct_0(X30)))))&(m1_pre_topc(k1_tex_2(X30,X31),X30)|(v2_struct_0(X30)|~l1_pre_topc(X30)|~m1_subset_1(X31,u1_struct_0(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tex_2])])])])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_22])]), c_0_43]), c_0_44])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_43])).
% 0.19/0.39  cnf(c_0_61, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_46]), c_0_43])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (k6_domain_1(u1_struct_0(esk3_0),esk1_1(esk3_0))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_46]), c_0_47])]), c_0_43])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_22])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_25])])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk3_0)|~r1_tarski(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_54]), c_0_55])])).
% 0.19/0.39  cnf(c_0_68, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (l1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_55])).
% 0.19/0.39  cnf(c_0_70, plain, (u1_struct_0(X1)=k6_domain_1(u1_struct_0(X2),X3)|v2_struct_0(X1)|v2_struct_0(X2)|X1!=k1_tex_2(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.39  cnf(c_0_71, plain, (m1_pre_topc(k1_tex_2(X1,X2),X1)|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.39  cnf(c_0_72, plain, (v1_pre_topc(k1_tex_2(X1,X2))|v2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.39  cnf(c_0_73, plain, (v2_struct_0(X1)|~v2_struct_0(k1_tex_2(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.39  cnf(c_0_74, negated_conjecture, (m1_subset_1(esk1_1(esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (k2_tarski(esk1_1(esk3_0),esk1_1(esk3_0))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_60]), c_0_62]), c_0_63])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_64]), c_0_44])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_65]), c_0_25])])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_54]), c_0_55])])).
% 0.19/0.39  cnf(c_0_80, plain, (X1=k1_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|u1_struct_0(X1)!=k6_domain_1(u1_struct_0(X2),X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.39  cnf(c_0_81, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))|~v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.39  cnf(c_0_83, plain, (k6_domain_1(u1_struct_0(X1),X2)=u1_struct_0(k1_tex_2(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_70]), c_0_71]), c_0_72]), c_0_73])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk1_1(esk3_0))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_74]), c_0_75]), c_0_76])).
% 0.19/0.39  cnf(c_0_85, negated_conjecture, (l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.39  cnf(c_0_86, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))),esk3_0)), inference(rw,[status(thm)],[c_0_65, c_0_78])).
% 0.19/0.39  cnf(c_0_87, negated_conjecture, (m1_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(rw,[status(thm)],[c_0_79, c_0_78])).
% 0.19/0.39  cnf(c_0_88, negated_conjecture, (X1=k1_tex_2(esk3_0,esk1_1(esk3_0))|v2_struct_0(X1)|u1_struct_0(X1)!=u1_struct_0(esk3_0)|~v1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_63]), c_0_60]), c_0_25])]), c_0_43])).
% 0.19/0.39  cnf(c_0_89, negated_conjecture, (v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_30]), c_0_25])])).
% 0.19/0.39  cnf(c_0_90, negated_conjecture, (~v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_78]), c_0_62])).
% 0.19/0.39  cnf(c_0_91, negated_conjecture, (m1_pre_topc(k1_tex_2(esk3_0,esk1_1(esk3_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_60]), c_0_25])]), c_0_43])).
% 0.19/0.39  cnf(c_0_92, negated_conjecture, (u1_struct_0(k1_tex_2(esk3_0,esk1_1(esk3_0)))=u1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_60]), c_0_63]), c_0_25])]), c_0_43])).
% 0.19/0.39  cnf(c_0_93, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))!=g1_pre_topc(u1_struct_0(k1_tex_2(esk2_0,X1)),u1_pre_topc(k1_tex_2(esk2_0,X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_94, negated_conjecture, (u1_struct_0(k1_tex_2(esk2_0,esk1_1(esk3_0)))=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_74]), c_0_22])]), c_0_44]), c_0_84])).
% 0.19/0.39  cnf(c_0_95, negated_conjecture, (X1=k1_tex_2(esk2_0,esk1_1(esk3_0))|v2_struct_0(X1)|u1_struct_0(X1)!=u1_struct_0(esk3_0)|~v1_pre_topc(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_84]), c_0_74]), c_0_22])]), c_0_44])).
% 0.19/0.39  cnf(c_0_96, negated_conjecture, (m1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_21]), c_0_22])])).
% 0.19/0.39  cnf(c_0_97, negated_conjecture, (l1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(spm,[status(thm)],[c_0_34, c_0_85])).
% 0.19/0.39  cnf(c_0_98, negated_conjecture, (r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_86]), c_0_25])])).
% 0.19/0.39  cnf(c_0_99, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_87]), c_0_85])])).
% 0.19/0.39  cnf(c_0_100, negated_conjecture, (k1_tex_2(esk3_0,esk1_1(esk3_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_78]), c_0_89]), c_0_40])]), c_0_90])).
% 0.19/0.39  cnf(c_0_101, negated_conjecture, (v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k1_tex_2(esk3_0,esk1_1(esk3_0)))))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_91]), c_0_25])]), c_0_92])).
% 0.19/0.39  cnf(c_0_102, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(k1_tex_2(esk2_0,esk1_1(esk3_0))))!=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_74])])).
% 0.19/0.39  cnf(c_0_103, negated_conjecture, (k1_tex_2(esk2_0,esk1_1(esk3_0))=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_78]), c_0_89]), c_0_96])]), c_0_90])).
% 0.19/0.39  cnf(c_0_104, negated_conjecture, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))|~v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(spm,[status(thm)],[c_0_68, c_0_97])).
% 0.19/0.39  cnf(c_0_105, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_98]), c_0_99])])).
% 0.19/0.39  cnf(c_0_106, negated_conjecture, (X1=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))|v2_struct_0(X1)|u1_struct_0(X1)!=u1_struct_0(esk3_0)|~v1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)), inference(rw,[status(thm)],[c_0_88, c_0_100])).
% 0.19/0.39  cnf(c_0_107, negated_conjecture, (v1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(rw,[status(thm)],[c_0_101, c_0_100])).
% 0.19/0.39  cnf(c_0_108, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))!=g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.19/0.39  cnf(c_0_109, negated_conjecture, (~v2_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105]), c_0_62])).
% 0.19/0.39  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_105]), c_0_107]), c_0_86])]), c_0_108]), c_0_109]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 111
% 0.19/0.39  # Proof object clause steps            : 78
% 0.19/0.39  # Proof object formula steps           : 33
% 0.19/0.39  # Proof object conjectures             : 58
% 0.19/0.39  # Proof object clause conjectures      : 55
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 26
% 0.19/0.39  # Proof object initial formulas used   : 16
% 0.19/0.39  # Proof object generating inferences   : 40
% 0.19/0.39  # Proof object simplifying inferences  : 99
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 16
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 30
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 29
% 0.19/0.39  # Processed clauses                    : 313
% 0.19/0.39  # ...of these trivial                  : 32
% 0.19/0.39  # ...subsumed                          : 31
% 0.19/0.39  # ...remaining for further processing  : 249
% 0.19/0.39  # Other redundant clauses eliminated   : 3
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 80
% 0.19/0.39  # Generated clauses                    : 480
% 0.19/0.39  # ...of the previous two non-trivial   : 458
% 0.19/0.39  # Contextual simplify-reflections      : 4
% 0.19/0.39  # Paramodulations                      : 473
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 7
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 137
% 0.19/0.39  #    Positive orientable unit clauses  : 74
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 16
% 0.19/0.39  #    Non-unit-clauses                  : 47
% 0.19/0.39  # Current number of unprocessed clauses: 150
% 0.19/0.39  # ...number of literals in the above   : 341
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 110
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 466
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 208
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 17
% 0.19/0.39  # Unit Clause-clause subsumption calls : 48
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 156
% 0.19/0.39  # BW rewrite match successes           : 11
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 15985
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.045 s
% 0.19/0.39  # System time              : 0.006 s
% 0.19/0.39  # Total time               : 0.051 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
