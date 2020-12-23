%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:10 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 172 expanded)
%              Number of clauses        :   53 (  75 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  187 ( 345 expanded)
%              Number of equality atoms :   65 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t2_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
         => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(t6_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
              & v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc12_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(c_0_23,plain,(
    ! [X34,X35] : k1_setfam_1(k2_tarski(X34,X35)) = k3_xboole_0(X34,X35) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_24,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X47,X48] :
      ( v1_xboole_0(X47)
      | ~ v1_zfmisc_1(X47)
      | v1_xboole_0(k3_xboole_0(X47,X48))
      | r1_tarski(X47,X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_tex_2])])])])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ~ ( v1_subset_1(k6_domain_1(X1,X2),X1)
                & v1_zfmisc_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tex_2])).

fof(c_0_30,plain,(
    ! [X23,X24] :
      ( ( ~ r1_xboole_0(X23,X24)
        | k4_xboole_0(X23,X24) = X23 )
      & ( k4_xboole_0(X23,X24) != X23
        | r1_xboole_0(X23,X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X25,X26] : k2_tarski(X25,X26) = k2_tarski(X26,X25) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k3_xboole_0(X1,X2))
    | r1_tarski(X1,X2)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk4_0,esk3_0)
    & v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0)
    & v1_zfmisc_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X14] :
      ( ~ v1_xboole_0(X14)
      | X14 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X1,X2)
    | v1_xboole_0(k1_setfam_1(k1_enumset1(X1,X1,X2)))
    | ~ v1_zfmisc_1(X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X30,X31] : k3_tarski(k2_tarski(X30,X31)) = k2_xboole_0(X30,X31) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_44,plain,(
    ! [X43,X44] :
      ( v1_xboole_0(X43)
      | ~ m1_subset_1(X44,X43)
      | k6_domain_1(X43,X44) = k1_tarski(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_45,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) != X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_27]),c_0_27])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | v1_xboole_0(k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

fof(c_0_50,plain,(
    ! [X20] : k5_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_51,plain,(
    ! [X40,X41] :
      ( v1_xboole_0(X40)
      | ~ m1_subset_1(X41,X40)
      | m1_subset_1(k6_domain_1(X40,X41),k1_zfmisc_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_52,plain,(
    ! [X32,X33] : k2_xboole_0(k1_tarski(X32),X33) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_53,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_56,plain,(
    ! [X21,X22] :
      ( v1_xboole_0(X22)
      | ~ r1_tarski(X22,X21)
      | ~ r1_xboole_0(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X2,X2,X1))) != X1 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1)) = k1_xboole_0
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_60,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X36,k1_zfmisc_1(X37))
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | m1_subset_1(X36,k1_zfmisc_1(X37)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_27])).

cnf(c_0_65,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_27])).

fof(c_0_66,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | r1_tarski(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_42])).

cnf(c_0_71,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_55]),c_0_27]),c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k1_enumset1(esk4_0,esk4_0,esk4_0) = k6_domain_1(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_62]),c_0_42])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_74,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | v1_xboole_0(X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k6_domain_1(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k3_tarski(k1_enumset1(k6_domain_1(esk3_0,esk4_0),k6_domain_1(esk3_0,esk4_0),X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_73,c_0_64])).

fof(c_0_79,plain,(
    ! [X39] :
      ( ~ l1_struct_0(X39)
      | ~ v1_subset_1(k2_struct_0(X39),u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).

fof(c_0_80,plain,(
    ! [X38] :
      ( ~ l1_struct_0(X38)
      | k2_struct_0(X38) = u1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_81,plain,(
    ! [X42] :
      ( ~ l1_orders_2(X42)
      | l1_struct_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_82,plain,(
    ! [X45] :
      ( v1_orders_2(k2_yellow_1(X45))
      & l1_orders_2(k2_yellow_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk3_0,k6_domain_1(esk3_0,esk4_0))
    | v1_xboole_0(k6_domain_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( k6_domain_1(esk3_0,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_86,plain,
    ( ~ l1_struct_0(X1)
    | ~ v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_88,plain,(
    ! [X46] :
      ( u1_struct_0(k2_yellow_1(X46)) = X46
      & u1_orders_2(k2_yellow_1(X46)) = k1_yellow_1(X46) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

cnf(c_0_89,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_90,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( k6_domain_1(esk3_0,esk4_0) = esk3_0
    | ~ r1_tarski(esk3_0,k6_domain_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_76])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk3_0,k6_domain_1(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_84]),c_0_85])).

cnf(c_0_93,plain,
    ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_95,plain,
    ( l1_struct_0(k2_yellow_1(X1)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_97,negated_conjecture,
    ( k6_domain_1(esk3_0,esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_98,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:48:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.030 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.38  fof(t2_tex_2, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 0.20/0.38  fof(t6_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 0.20/0.38  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.38  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.20/0.38  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.20/0.38  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.20/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.38  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(fc12_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>~(v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 0.20/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.38  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.38  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.38  fof(c_0_23, plain, ![X34, X35]:k1_setfam_1(k2_tarski(X34,X35))=k3_xboole_0(X34,X35), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.38  fof(c_0_24, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.38  fof(c_0_25, plain, ![X17, X18]:k4_xboole_0(X17,X18)=k5_xboole_0(X17,k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.38  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  fof(c_0_28, plain, ![X47, X48]:(v1_xboole_0(X47)|~v1_zfmisc_1(X47)|(v1_xboole_0(k3_xboole_0(X47,X48))|r1_tarski(X47,X48))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_tex_2])])])])).
% 0.20/0.38  fof(c_0_29, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,X1)=>~((v1_subset_1(k6_domain_1(X1,X2),X1)&v1_zfmisc_1(X1)))))), inference(assume_negation,[status(cth)],[t6_tex_2])).
% 0.20/0.38  fof(c_0_30, plain, ![X23, X24]:((~r1_xboole_0(X23,X24)|k4_xboole_0(X23,X24)=X23)&(k4_xboole_0(X23,X24)!=X23|r1_xboole_0(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.38  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.38  cnf(c_0_32, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.38  fof(c_0_33, plain, ![X25, X26]:k2_tarski(X25,X26)=k2_tarski(X26,X25), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.38  cnf(c_0_34, plain, (v1_xboole_0(X1)|v1_xboole_0(k3_xboole_0(X1,X2))|r1_tarski(X1,X2)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  fof(c_0_35, negated_conjecture, (~v1_xboole_0(esk3_0)&(m1_subset_1(esk4_0,esk3_0)&(v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0)&v1_zfmisc_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).
% 0.20/0.38  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.38  cnf(c_0_38, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.38  fof(c_0_39, plain, ![X14]:(~v1_xboole_0(X14)|X14=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.38  cnf(c_0_40, plain, (v1_xboole_0(X1)|r1_tarski(X1,X2)|v1_xboole_0(k1_setfam_1(k1_enumset1(X1,X1,X2)))|~v1_zfmisc_1(X1)), inference(rw,[status(thm)],[c_0_34, c_0_32])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  fof(c_0_43, plain, ![X30, X31]:k3_tarski(k2_tarski(X30,X31))=k2_xboole_0(X30,X31), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.38  fof(c_0_44, plain, ![X43, X44]:(v1_xboole_0(X43)|~m1_subset_1(X44,X43)|k6_domain_1(X43,X44)=k1_tarski(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.38  fof(c_0_45, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.38  cnf(c_0_46, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))!=X1), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_47, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_27]), c_0_27])).
% 0.20/0.38  cnf(c_0_48, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(esk3_0,X1)|v1_xboole_0(k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.20/0.38  fof(c_0_50, plain, ![X20]:k5_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.38  fof(c_0_51, plain, ![X40, X41]:(v1_xboole_0(X40)|~m1_subset_1(X41,X40)|m1_subset_1(k6_domain_1(X40,X41),k1_zfmisc_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.20/0.38  fof(c_0_52, plain, ![X32, X33]:k2_xboole_0(k1_tarski(X32),X33)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.20/0.38  cnf(c_0_53, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.38  cnf(c_0_54, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_55, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  fof(c_0_56, plain, ![X21, X22]:(v1_xboole_0(X22)|(~r1_tarski(X22,X21)|~r1_xboole_0(X22,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.20/0.38  cnf(c_0_57, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X2,X2,X1)))!=X1), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (k1_setfam_1(k1_enumset1(esk3_0,esk3_0,X1))=k1_xboole_0|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.38  cnf(c_0_59, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.38  fof(c_0_60, plain, ![X36, X37]:((~m1_subset_1(X36,k1_zfmisc_1(X37))|r1_tarski(X36,X37))&(~r1_tarski(X36,X37)|m1_subset_1(X36,k1_zfmisc_1(X37)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.38  cnf(c_0_61, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_63, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.38  cnf(c_0_64, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_27])).
% 0.20/0.38  cnf(c_0_65, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_27])).
% 0.20/0.38  fof(c_0_66, plain, ![X19]:k2_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.20/0.38  cnf(c_0_67, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, (r1_xboole_0(X1,esk3_0)|r1_tarski(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.20/0.38  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (m1_subset_1(k6_domain_1(esk3_0,esk4_0),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_42])).
% 0.20/0.38  cnf(c_0_71, plain, (k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),X2))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_55]), c_0_27]), c_0_64])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (k1_enumset1(esk4_0,esk4_0,esk4_0)=k6_domain_1(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_62]), c_0_42])).
% 0.20/0.38  cnf(c_0_73, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.38  fof(c_0_74, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (r1_tarski(esk3_0,X1)|v1_xboole_0(X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (r1_tarski(k6_domain_1(esk3_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, (k3_tarski(k1_enumset1(k6_domain_1(esk3_0,esk4_0),k6_domain_1(esk3_0,esk4_0),X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.38  cnf(c_0_78, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_73, c_0_64])).
% 0.20/0.38  fof(c_0_79, plain, ![X39]:(~l1_struct_0(X39)|~v1_subset_1(k2_struct_0(X39),u1_struct_0(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc12_struct_0])])])).
% 0.20/0.38  fof(c_0_80, plain, ![X38]:(~l1_struct_0(X38)|k2_struct_0(X38)=u1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.38  fof(c_0_81, plain, ![X42]:(~l1_orders_2(X42)|l1_struct_0(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.38  fof(c_0_82, plain, ![X45]:(v1_orders_2(k2_yellow_1(X45))&l1_orders_2(k2_yellow_1(X45))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.38  cnf(c_0_83, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.38  cnf(c_0_84, negated_conjecture, (r1_tarski(esk3_0,k6_domain_1(esk3_0,esk4_0))|v1_xboole_0(k6_domain_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.38  cnf(c_0_85, negated_conjecture, (k6_domain_1(esk3_0,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.38  cnf(c_0_86, plain, (~l1_struct_0(X1)|~v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.38  cnf(c_0_87, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.38  fof(c_0_88, plain, ![X46]:(u1_struct_0(k2_yellow_1(X46))=X46&u1_orders_2(k2_yellow_1(X46))=k1_yellow_1(X46)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.38  cnf(c_0_89, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.38  cnf(c_0_90, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.38  cnf(c_0_91, negated_conjecture, (k6_domain_1(esk3_0,esk4_0)=esk3_0|~r1_tarski(esk3_0,k6_domain_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_83, c_0_76])).
% 0.20/0.38  cnf(c_0_92, negated_conjecture, (r1_tarski(esk3_0,k6_domain_1(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_84]), c_0_85])).
% 0.20/0.38  cnf(c_0_93, plain, (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X1))|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.38  cnf(c_0_94, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.38  cnf(c_0_95, plain, (l1_struct_0(k2_yellow_1(X1))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.38  cnf(c_0_96, negated_conjecture, (v1_subset_1(k6_domain_1(esk3_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_97, negated_conjecture, (k6_domain_1(esk3_0,esk4_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 0.20/0.38  cnf(c_0_98, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])])).
% 0.20/0.38  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_98]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 100
% 0.20/0.38  # Proof object clause steps            : 53
% 0.20/0.38  # Proof object formula steps           : 47
% 0.20/0.38  # Proof object conjectures             : 21
% 0.20/0.38  # Proof object clause conjectures      : 18
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 26
% 0.20/0.38  # Proof object initial formulas used   : 23
% 0.20/0.38  # Proof object generating inferences   : 16
% 0.20/0.38  # Proof object simplifying inferences  : 25
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 25
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 37
% 0.20/0.38  # Removed in clause preprocessing      : 6
% 0.20/0.38  # Initial clauses in saturation        : 31
% 0.20/0.38  # Processed clauses                    : 164
% 0.20/0.38  # ...of these trivial                  : 3
% 0.20/0.38  # ...subsumed                          : 60
% 0.20/0.38  # ...remaining for further processing  : 101
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 37
% 0.20/0.38  # Generated clauses                    : 252
% 0.20/0.38  # ...of the previous two non-trivial   : 248
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 250
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 60
% 0.20/0.38  #    Positive orientable unit clauses  : 11
% 0.20/0.38  #    Positive unorientable unit clauses: 1
% 0.20/0.38  #    Negative unit clauses             : 6
% 0.20/0.38  #    Non-unit-clauses                  : 42
% 0.20/0.38  # Current number of unprocessed clauses: 84
% 0.20/0.38  # ...number of literals in the above   : 239
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 45
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 682
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 585
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 41
% 0.20/0.38  # Unit Clause-clause subsumption calls : 51
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 16
% 0.20/0.38  # BW rewrite match successes           : 12
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 5639
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.037 s
% 0.20/0.38  # System time              : 0.007 s
% 0.20/0.38  # Total time               : 0.043 s
% 0.20/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
