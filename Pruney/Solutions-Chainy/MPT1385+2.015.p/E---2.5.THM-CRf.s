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
% DateTime   : Thu Dec  3 11:14:33 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 354 expanded)
%              Number of clauses        :   47 ( 131 expanded)
%              Number of leaves         :   17 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  255 (1357 expanded)
%              Number of equality atoms :   26 ( 132 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t10_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))
              <=> m1_connsp_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(d2_connsp_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,X2)
              <=> r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(dt_m2_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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

fof(c_0_17,plain,(
    ! [X43,X44] :
      ( v1_xboole_0(X43)
      | ~ m1_subset_1(X44,X43)
      | k6_domain_1(X43,X44) = k1_tarski(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_18,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_20,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_21,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_22,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k5_enumset1(X23,X23,X24,X25,X26,X27,X28) = k4_enumset1(X23,X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_24,plain,(
    ! [X29,X30,X31,X32,X33,X34,X35] : k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35) = k5_enumset1(X29,X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))
                <=> m1_connsp_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_connsp_2])).

fof(c_0_26,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,X38)
        | ~ r1_tarski(k2_tarski(X36,X37),X38) )
      & ( r2_hidden(X37,X38)
        | ~ r1_tarski(k2_tarski(X36,X37),X38) )
      & ( ~ r2_hidden(X36,X38)
        | ~ r2_hidden(X37,X38)
        | r1_tarski(k2_tarski(X36,X37),X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
      | ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) )
    & ( m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
      | m1_connsp_2(esk3_0,esk1_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_39,plain,(
    ! [X48,X49,X50] :
      ( ( ~ m2_connsp_2(X50,X48,X49)
        | r1_tarski(X49,k1_tops_1(X48,X50))
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( ~ r1_tarski(X49,k1_tops_1(X48,X50))
        | m2_connsp_2(X50,X48,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).

fof(c_0_40,plain,(
    ! [X54,X55,X56] :
      ( ~ v2_pre_topc(X54)
      | ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | ~ m2_connsp_2(X56,X54,X55)
      | m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k6_domain_1(u1_struct_0(esk1_0),esk2_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r1_tarski(X3,k1_tops_1(X2,X1))
    | ~ m2_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m2_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_45,plain,(
    ! [X41,X42] :
      ( v1_xboole_0(X41)
      | ~ m1_subset_1(X42,X41)
      | m1_subset_1(k6_domain_1(X41,X42),k1_zfmisc_1(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_46,plain,(
    ! [X45,X46,X47] :
      ( ( ~ m1_connsp_2(X47,X45,X46)
        | r2_hidden(X46,k1_tops_1(X45,X47))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( ~ r2_hidden(X46,k1_tops_1(X45,X47))
        | m1_connsp_2(X47,X45,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_subset_1(X46,u1_struct_0(X45))
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_47,plain,(
    ! [X51,X52,X53] :
      ( v2_struct_0(X51)
      | ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | ~ m1_subset_1(X52,u1_struct_0(X51))
      | ~ m1_connsp_2(X53,X51,X52)
      | m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,X1)
    | ~ r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,k1_tops_1(X1,X2))
    | ~ m2_connsp_2(X2,X1,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_38])).

cnf(c_0_55,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_59,plain,(
    ! [X40] :
      ( v2_struct_0(X40)
      | ~ l1_struct_0(X40)
      | ~ v1_xboole_0(u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_60,plain,(
    ! [X39] :
      ( ~ l1_pre_topc(X39)
      | l1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_61,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ m2_connsp_2(X1,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_64,negated_conjecture,
    ( m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))
    | ~ m1_connsp_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_38]),c_0_55]),c_0_56])]),c_0_58])).

cnf(c_0_66,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk1_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k1_tops_1(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55]),c_0_56])]),c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_71,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk1_0,esk2_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_38])])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1)
    | ~ r2_hidden(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_42])).

cnf(c_0_75,negated_conjecture,
    ( ~ m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_76,negated_conjecture,
    ( m1_connsp_2(esk3_0,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_56])]),c_0_58])).

cnf(c_0_77,plain,
    ( m2_connsp_2(X3,X2,X1)
    | ~ r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( ~ m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_55]),c_0_62]),c_0_56])]),c_0_79]),c_0_54])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_80]),c_0_56])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n007.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 20:46:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.36  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.028 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.36  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.36  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.36  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.36  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.13/0.36  fof(t10_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_connsp_2)).
% 0.13/0.36  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.13/0.36  fof(d2_connsp_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,X2)<=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 0.13/0.36  fof(dt_m2_connsp_2, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m2_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 0.13/0.36  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.13/0.36  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.13/0.36  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.13/0.36  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.36  fof(c_0_17, plain, ![X43, X44]:(v1_xboole_0(X43)|~m1_subset_1(X44,X43)|k6_domain_1(X43,X44)=k1_tarski(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.36  fof(c_0_18, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.36  fof(c_0_19, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.36  fof(c_0_20, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.36  fof(c_0_21, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.36  fof(c_0_22, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.36  fof(c_0_23, plain, ![X23, X24, X25, X26, X27, X28]:k5_enumset1(X23,X23,X24,X25,X26,X27,X28)=k4_enumset1(X23,X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.36  fof(c_0_24, plain, ![X29, X30, X31, X32, X33, X34, X35]:k6_enumset1(X29,X29,X30,X31,X32,X33,X34,X35)=k5_enumset1(X29,X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.13/0.36  fof(c_0_25, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2)))))), inference(assume_negation,[status(cth)],[t10_connsp_2])).
% 0.13/0.36  fof(c_0_26, plain, ![X36, X37, X38]:(((r2_hidden(X36,X38)|~r1_tarski(k2_tarski(X36,X37),X38))&(r2_hidden(X37,X38)|~r1_tarski(k2_tarski(X36,X37),X38)))&(~r2_hidden(X36,X38)|~r2_hidden(X37,X38)|r1_tarski(k2_tarski(X36,X37),X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.13/0.36  cnf(c_0_27, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.36  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.36  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.36  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.36  cnf(c_0_32, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.36  cnf(c_0_33, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.36  cnf(c_0_34, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.36  fof(c_0_35, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|~m1_connsp_2(esk3_0,esk1_0,esk2_0))&(m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|m1_connsp_2(esk3_0,esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_25])])])])).
% 0.13/0.36  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.36  cnf(c_0_37, plain, (k6_domain_1(X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  fof(c_0_39, plain, ![X48, X49, X50]:((~m2_connsp_2(X50,X48,X49)|r1_tarski(X49,k1_tops_1(X48,X50))|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|(~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(~r1_tarski(X49,k1_tops_1(X48,X50))|m2_connsp_2(X50,X48,X49)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|(~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).
% 0.13/0.36  fof(c_0_40, plain, ![X54, X55, X56]:(~v2_pre_topc(X54)|~l1_pre_topc(X54)|~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|(~m2_connsp_2(X56,X54,X55)|m1_subset_1(X56,k1_zfmisc_1(u1_struct_0(X54))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).
% 0.13/0.36  cnf(c_0_41, plain, (r2_hidden(X1,X2)|~r1_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.13/0.36  cnf(c_0_42, negated_conjecture, (k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k6_domain_1(u1_struct_0(esk1_0),esk2_0)|v1_xboole_0(u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.36  cnf(c_0_43, plain, (r1_tarski(X3,k1_tops_1(X2,X1))|~m2_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.36  cnf(c_0_44, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m2_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.36  fof(c_0_45, plain, ![X41, X42]:(v1_xboole_0(X41)|~m1_subset_1(X42,X41)|m1_subset_1(k6_domain_1(X41,X42),k1_zfmisc_1(X41))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.13/0.36  fof(c_0_46, plain, ![X45, X46, X47]:((~m1_connsp_2(X47,X45,X46)|r2_hidden(X46,k1_tops_1(X45,X47))|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_subset_1(X46,u1_struct_0(X45))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(~r2_hidden(X46,k1_tops_1(X45,X47))|m1_connsp_2(X47,X45,X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_subset_1(X46,u1_struct_0(X45))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.13/0.36  fof(c_0_47, plain, ![X51, X52, X53]:(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)|~m1_subset_1(X52,u1_struct_0(X51))|(~m1_connsp_2(X53,X51,X52)|m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.13/0.36  cnf(c_0_48, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,X1)|~r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.36  cnf(c_0_49, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X1)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_43, c_0_44])).
% 0.13/0.36  cnf(c_0_50, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.36  cnf(c_0_51, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.36  cnf(c_0_52, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.36  cnf(c_0_53, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,k1_tops_1(X1,X2))|~m2_connsp_2(X2,X1,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|~v2_pre_topc(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.36  cnf(c_0_54, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|v1_xboole_0(u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_50, c_0_38])).
% 0.13/0.36  cnf(c_0_55, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_56, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_57, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.36  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  fof(c_0_59, plain, ![X40]:(v2_struct_0(X40)|~l1_struct_0(X40)|~v1_xboole_0(u1_struct_0(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.36  fof(c_0_60, plain, ![X39]:(~l1_pre_topc(X39)|l1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.36  cnf(c_0_61, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.36  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_63, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~m2_connsp_2(X1,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])])).
% 0.13/0.36  cnf(c_0_64, negated_conjecture, (m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_0,k1_tops_1(esk1_0,X1))|~m1_connsp_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_38]), c_0_55]), c_0_56])]), c_0_58])).
% 0.13/0.36  cnf(c_0_66, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.36  cnf(c_0_67, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.36  cnf(c_0_68, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.36  cnf(c_0_69, negated_conjecture, (m1_connsp_2(esk3_0,esk1_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~r2_hidden(X1,k1_tops_1(esk1_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_55]), c_0_56])]), c_0_58])).
% 0.13/0.36  cnf(c_0_70, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r2_hidden(esk2_0,k1_tops_1(esk1_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])).
% 0.13/0.36  cnf(c_0_71, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.13/0.36  cnf(c_0_72, plain, (v2_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.13/0.36  cnf(c_0_73, negated_conjecture, (m1_connsp_2(esk3_0,esk1_0,esk2_0)|v1_xboole_0(u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_38])])).
% 0.13/0.36  cnf(c_0_74, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),X1)|~r2_hidden(esk2_0,X1)), inference(spm,[status(thm)],[c_0_71, c_0_42])).
% 0.13/0.36  cnf(c_0_75, negated_conjecture, (~m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))|~m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.36  cnf(c_0_76, negated_conjecture, (m1_connsp_2(esk3_0,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_56])]), c_0_58])).
% 0.13/0.36  cnf(c_0_77, plain, (m2_connsp_2(X3,X2,X1)|~r1_tarski(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.36  cnf(c_0_78, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|r1_tarski(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_74, c_0_70])).
% 0.13/0.36  cnf(c_0_79, negated_conjecture, (~m2_connsp_2(esk3_0,esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.13/0.36  cnf(c_0_80, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_55]), c_0_62]), c_0_56])]), c_0_79]), c_0_54])).
% 0.13/0.36  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_80]), c_0_56])]), c_0_58]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 82
% 0.13/0.36  # Proof object clause steps            : 47
% 0.13/0.36  # Proof object formula steps           : 35
% 0.13/0.36  # Proof object conjectures             : 25
% 0.13/0.36  # Proof object clause conjectures      : 22
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 26
% 0.13/0.36  # Proof object initial formulas used   : 17
% 0.13/0.36  # Proof object generating inferences   : 15
% 0.13/0.36  # Proof object simplifying inferences  : 49
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 17
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 27
% 0.13/0.36  # Removed in clause preprocessing      : 7
% 0.13/0.36  # Initial clauses in saturation        : 20
% 0.13/0.36  # Processed clauses                    : 74
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 3
% 0.13/0.36  # ...remaining for further processing  : 71
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 2
% 0.13/0.36  # Backward-rewritten                   : 14
% 0.13/0.36  # Generated clauses                    : 70
% 0.13/0.36  # ...of the previous two non-trivial   : 57
% 0.13/0.36  # Contextual simplify-reflections      : 4
% 0.13/0.36  # Paramodulations                      : 68
% 0.13/0.36  # Factorizations                       : 2
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 35
% 0.13/0.36  #    Positive orientable unit clauses  : 6
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 2
% 0.13/0.36  #    Non-unit-clauses                  : 27
% 0.13/0.36  # Current number of unprocessed clauses: 23
% 0.13/0.36  # ...number of literals in the above   : 120
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 43
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 475
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 88
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 7
% 0.13/0.36  # Unit Clause-clause subsumption calls : 12
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 3
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 4621
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.032 s
% 0.13/0.36  # System time              : 0.004 s
% 0.13/0.36  # Total time               : 0.036 s
% 0.13/0.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
