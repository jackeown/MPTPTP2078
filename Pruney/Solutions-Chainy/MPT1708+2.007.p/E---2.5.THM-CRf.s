%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 406 expanded)
%              Number of clauses        :   58 ( 143 expanded)
%              Number of leaves         :   19 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          :  324 (2913 expanded)
%              Number of equality atoms :   50 ( 441 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & v1_pre_topc(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( X4 = k2_tsep_1(X1,X2,X3)
                    <=> u1_struct_0(X4) = k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

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

fof(dt_k2_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
        & v1_pre_topc(k2_tsep_1(X1,X2,X3))
        & m1_pre_topc(k2_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(t17_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( ~ r1_tsep_1(X2,X3)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))
                   => ( ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                          & X5 = X4 )
                      & ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                          & X5 = X4 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tmap_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_19,plain,(
    ! [X45,X46] : k1_setfam_1(k2_tarski(X45,X46)) = k3_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X54,X55,X56,X57] :
      ( ( X57 != k2_tsep_1(X54,X55,X56)
        | u1_struct_0(X57) = k3_xboole_0(u1_struct_0(X55),u1_struct_0(X56))
        | v2_struct_0(X57)
        | ~ v1_pre_topc(X57)
        | ~ m1_pre_topc(X57,X54)
        | r1_tsep_1(X55,X56)
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X56,X54)
        | v2_struct_0(X55)
        | ~ m1_pre_topc(X55,X54)
        | v2_struct_0(X54)
        | ~ l1_pre_topc(X54) )
      & ( u1_struct_0(X57) != k3_xboole_0(u1_struct_0(X55),u1_struct_0(X56))
        | X57 = k2_tsep_1(X54,X55,X56)
        | v2_struct_0(X57)
        | ~ v1_pre_topc(X57)
        | ~ m1_pre_topc(X57,X54)
        | r1_tsep_1(X55,X56)
        | v2_struct_0(X56)
        | ~ m1_pre_topc(X56,X54)
        | v2_struct_0(X55)
        | ~ m1_pre_topc(X55,X54)
        | v2_struct_0(X54)
        | ~ l1_pre_topc(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36] : k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36) = k5_enumset1(X30,X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_29,plain,
    ( u1_struct_0(X1) = k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X58,X59,X60] :
      ( ( ~ v2_struct_0(k2_tsep_1(X58,X59,X60))
        | v2_struct_0(X58)
        | ~ l1_pre_topc(X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X58)
        | v2_struct_0(X60)
        | ~ m1_pre_topc(X60,X58) )
      & ( v1_pre_topc(k2_tsep_1(X58,X59,X60))
        | v2_struct_0(X58)
        | ~ l1_pre_topc(X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X58)
        | v2_struct_0(X60)
        | ~ m1_pre_topc(X60,X58) )
      & ( m1_pre_topc(k2_tsep_1(X58,X59,X60),X58)
        | v2_struct_0(X58)
        | ~ l1_pre_topc(X58)
        | v2_struct_0(X59)
        | ~ m1_pre_topc(X59,X58)
        | v2_struct_0(X60)
        | ~ m1_pre_topc(X60,X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( ~ r1_tsep_1(X2,X3)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))
                     => ( ? [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                            & X5 = X4 )
                        & ? [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                            & X5 = X4 ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_tmap_1])).

cnf(c_0_38,plain,
    ( u1_struct_0(X1) = k1_setfam_1(k6_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | r1_tsep_1(X3,X4)
    | X1 != k2_tsep_1(X2,X3,X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_39,plain,
    ( m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( v1_pre_topc(k2_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,negated_conjecture,(
    ! [X68,X69] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & m1_pre_topc(esk2_0,esk1_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk1_0)
      & ~ r1_tsep_1(esk2_0,esk3_0)
      & m1_subset_1(esk4_0,u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)))
      & ( ~ m1_subset_1(X68,u1_struct_0(esk2_0))
        | X68 != esk4_0
        | ~ m1_subset_1(X69,u1_struct_0(esk3_0))
        | X69 != esk4_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])])).

fof(c_0_43,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X42))
      | k9_subset_1(X42,X43,X44) = k3_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_44,plain,(
    ! [X8,X9] : r1_tarski(k3_xboole_0(X8,X9),X8) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_45,plain,
    ( u1_struct_0(k2_tsep_1(X1,X2,X3)) = k1_setfam_1(k6_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))
    | r1_tsep_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39]),c_0_40]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(X39))
      | m1_subset_1(k9_subset_1(X39,X40,X41),k1_zfmisc_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_51,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk3_0))) = u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))
    | r1_tsep_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_48]),c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tsep_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

fof(c_0_59,plain,(
    ! [X61,X62,X63] :
      ( ( ~ r1_tarski(u1_struct_0(X62),u1_struct_0(X63))
        | m1_pre_topc(X62,X63)
        | ~ m1_pre_topc(X63,X61)
        | ~ m1_pre_topc(X62,X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) )
      & ( ~ m1_pre_topc(X62,X63)
        | r1_tarski(u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_pre_topc(X63,X61)
        | ~ m1_pre_topc(X62,X61)
        | ~ v2_pre_topc(X61)
        | ~ l1_pre_topc(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( k1_setfam_1(k6_enumset1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0))) = u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])).

fof(c_0_62,plain,(
    ! [X47,X48] :
      ( ( ~ m1_subset_1(X47,k1_zfmisc_1(X48))
        | r1_tarski(X47,X48) )
      & ( ~ r1_tarski(X47,X48)
        | m1_subset_1(X47,k1_zfmisc_1(X48)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_63,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_64,plain,(
    ! [X51,X52,X53] :
      ( v2_struct_0(X51)
      | ~ l1_pre_topc(X51)
      | v2_struct_0(X52)
      | ~ m1_pre_topc(X52,X51)
      | ~ m1_subset_1(X53,u1_struct_0(X52))
      | m1_subset_1(X53,u1_struct_0(X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_65,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_46]),c_0_47])]),c_0_49]),c_0_48])).

fof(c_0_68,plain,(
    ! [X49,X50] :
      ( ~ l1_pre_topc(X49)
      | ~ m1_pre_topc(X50,X49)
      | l1_pre_topc(X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_73,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_54]),c_0_56])).

cnf(c_0_75,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_76,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_78,plain,(
    ! [X38] : m1_subset_1(k2_subset_1(X38),k1_zfmisc_1(X38)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_79,plain,(
    ! [X37] : k2_subset_1(X37) = X37 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_54]),c_0_47])])).

cnf(c_0_82,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_54]),c_0_47])])).

cnf(c_0_83,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_77])).

cnf(c_0_84,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | X1 != esk4_0
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | X2 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_87,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))
    | m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])]),c_0_56])).

cnf(c_0_88,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_74]),c_0_75]),c_0_47])])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_87]),c_0_46]),c_0_54]),c_0_47])]),c_0_49]),c_0_56]),c_0_48])).

cnf(c_0_92,negated_conjecture,
    ( m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_46])])).

cnf(c_0_93,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_46]),c_0_47])])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_95,negated_conjecture,
    ( v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_92]),c_0_93])]),c_0_49]),c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_95]),c_0_46]),c_0_54]),c_0_47])]),c_0_49]),c_0_56]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.20/0.47  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.028 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.47  fof(d5_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k2_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k3_xboole_0(u1_struct_0(X2),u1_struct_0(X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tsep_1)).
% 0.20/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.47  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.47  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.47  fof(dt_k2_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k2_tsep_1(X1,X2,X3)))&v1_pre_topc(k2_tsep_1(X1,X2,X3)))&m1_pre_topc(k2_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 0.20/0.47  fof(t17_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_tmap_1)).
% 0.20/0.47  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.20/0.47  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.20/0.47  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.20/0.47  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.47  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.47  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.47  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.47  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.47  fof(c_0_19, plain, ![X45, X46]:k1_setfam_1(k2_tarski(X45,X46))=k3_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.47  fof(c_0_20, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.47  fof(c_0_21, plain, ![X54, X55, X56, X57]:((X57!=k2_tsep_1(X54,X55,X56)|u1_struct_0(X57)=k3_xboole_0(u1_struct_0(X55),u1_struct_0(X56))|(v2_struct_0(X57)|~v1_pre_topc(X57)|~m1_pre_topc(X57,X54))|r1_tsep_1(X55,X56)|(v2_struct_0(X56)|~m1_pre_topc(X56,X54))|(v2_struct_0(X55)|~m1_pre_topc(X55,X54))|(v2_struct_0(X54)|~l1_pre_topc(X54)))&(u1_struct_0(X57)!=k3_xboole_0(u1_struct_0(X55),u1_struct_0(X56))|X57=k2_tsep_1(X54,X55,X56)|(v2_struct_0(X57)|~v1_pre_topc(X57)|~m1_pre_topc(X57,X54))|r1_tsep_1(X55,X56)|(v2_struct_0(X56)|~m1_pre_topc(X56,X54))|(v2_struct_0(X55)|~m1_pre_topc(X55,X54))|(v2_struct_0(X54)|~l1_pre_topc(X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tsep_1])])])])])).
% 0.20/0.47  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.47  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.47  fof(c_0_24, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.47  fof(c_0_25, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.47  fof(c_0_26, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.47  fof(c_0_27, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.47  fof(c_0_28, plain, ![X30, X31, X32, X33, X34, X35, X36]:k6_enumset1(X30,X30,X31,X32,X33,X34,X35,X36)=k5_enumset1(X30,X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.47  cnf(c_0_29, plain, (u1_struct_0(X1)=k3_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|r1_tsep_1(X3,X4)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k2_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.47  cnf(c_0_30, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.47  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.47  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.47  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.47  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.47  fof(c_0_36, plain, ![X58, X59, X60]:(((~v2_struct_0(k2_tsep_1(X58,X59,X60))|(v2_struct_0(X58)|~l1_pre_topc(X58)|v2_struct_0(X59)|~m1_pre_topc(X59,X58)|v2_struct_0(X60)|~m1_pre_topc(X60,X58)))&(v1_pre_topc(k2_tsep_1(X58,X59,X60))|(v2_struct_0(X58)|~l1_pre_topc(X58)|v2_struct_0(X59)|~m1_pre_topc(X59,X58)|v2_struct_0(X60)|~m1_pre_topc(X60,X58))))&(m1_pre_topc(k2_tsep_1(X58,X59,X60),X58)|(v2_struct_0(X58)|~l1_pre_topc(X58)|v2_struct_0(X59)|~m1_pre_topc(X59,X58)|v2_struct_0(X60)|~m1_pre_topc(X60,X58)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_tsep_1])])])])).
% 0.20/0.47  fof(c_0_37, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(~(r1_tsep_1(X2,X3))=>![X4]:(m1_subset_1(X4,u1_struct_0(k2_tsep_1(X1,X2,X3)))=>(?[X5]:(m1_subset_1(X5,u1_struct_0(X2))&X5=X4)&?[X5]:(m1_subset_1(X5,u1_struct_0(X3))&X5=X4)))))))), inference(assume_negation,[status(cth)],[t17_tmap_1])).
% 0.20/0.47  cnf(c_0_38, plain, (u1_struct_0(X1)=k1_setfam_1(k6_enumset1(u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X4)))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|r1_tsep_1(X3,X4)|X1!=k2_tsep_1(X2,X3,X4)|~l1_pre_topc(X2)|~v1_pre_topc(X1)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.47  cnf(c_0_39, plain, (m1_pre_topc(k2_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_40, plain, (v1_pre_topc(k2_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_41, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k2_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  fof(c_0_42, negated_conjecture, ![X68, X69]:(((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&((~v2_struct_0(esk2_0)&m1_pre_topc(esk2_0,esk1_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&(~r1_tsep_1(esk2_0,esk3_0)&(m1_subset_1(esk4_0,u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)))&(~m1_subset_1(X68,u1_struct_0(esk2_0))|X68!=esk4_0|(~m1_subset_1(X69,u1_struct_0(esk3_0))|X69!=esk4_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_37])])])])])).
% 0.20/0.47  fof(c_0_43, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X42))|k9_subset_1(X42,X43,X44)=k3_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.20/0.47  fof(c_0_44, plain, ![X8, X9]:r1_tarski(k3_xboole_0(X8,X9),X8), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.20/0.47  cnf(c_0_45, plain, (u1_struct_0(k2_tsep_1(X1,X2,X3))=k1_setfam_1(k6_enumset1(u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3)))|r1_tsep_1(X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_39]), c_0_40]), c_0_41])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  fof(c_0_50, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(X39))|m1_subset_1(k9_subset_1(X39,X40,X41),k1_zfmisc_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.20/0.47  cnf(c_0_51, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.47  cnf(c_0_52, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.47  cnf(c_0_53, negated_conjecture, (k1_setfam_1(k6_enumset1(u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(esk3_0)))=u1_struct_0(k2_tsep_1(esk1_0,X1,esk3_0))|r1_tsep_1(X1,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])]), c_0_48]), c_0_49])).
% 0.20/0.47  cnf(c_0_54, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (~r1_tsep_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_57, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.47  cnf(c_0_58, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.47  fof(c_0_59, plain, ![X61, X62, X63]:((~r1_tarski(u1_struct_0(X62),u1_struct_0(X63))|m1_pre_topc(X62,X63)|~m1_pre_topc(X63,X61)|~m1_pre_topc(X62,X61)|(~v2_pre_topc(X61)|~l1_pre_topc(X61)))&(~m1_pre_topc(X62,X63)|r1_tarski(u1_struct_0(X62),u1_struct_0(X63))|~m1_pre_topc(X63,X61)|~m1_pre_topc(X62,X61)|(~v2_pre_topc(X61)|~l1_pre_topc(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.47  cnf(c_0_60, plain, (r1_tarski(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (k1_setfam_1(k6_enumset1(u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0)))=u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])).
% 0.20/0.47  fof(c_0_62, plain, ![X47, X48]:((~m1_subset_1(X47,k1_zfmisc_1(X48))|r1_tarski(X47,X48))&(~r1_tarski(X47,X48)|m1_subset_1(X47,k1_zfmisc_1(X48)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.47  cnf(c_0_63, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.47  fof(c_0_64, plain, ![X51, X52, X53]:(v2_struct_0(X51)|~l1_pre_topc(X51)|(v2_struct_0(X52)|~m1_pre_topc(X52,X51)|(~m1_subset_1(X53,u1_struct_0(X52))|m1_subset_1(X53,u1_struct_0(X51))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.47  cnf(c_0_65, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.47  cnf(c_0_66, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.47  cnf(c_0_67, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k2_tsep_1(esk1_0,X1,esk3_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_46]), c_0_47])]), c_0_49]), c_0_48])).
% 0.20/0.47  fof(c_0_68, plain, ![X49, X50]:(~l1_pre_topc(X49)|(~m1_pre_topc(X50,X49)|l1_pre_topc(X50))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.47  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (m1_subset_1(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),k1_zfmisc_1(X1))|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_63, c_0_61])).
% 0.20/0.47  cnf(c_0_71, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.47  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)|~v2_pre_topc(X1)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(esk2_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.47  cnf(c_0_74, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_54]), c_0_56])).
% 0.20/0.47  cnf(c_0_75, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_76, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, (r1_tarski(u1_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0)),X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.47  fof(c_0_78, plain, ![X38]:m1_subset_1(k2_subset_1(X38),k1_zfmisc_1(X38)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.47  fof(c_0_79, plain, ![X37]:k2_subset_1(X37)=X37, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.47  cnf(c_0_80, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|v2_struct_0(X1)|m1_subset_1(esk4_0,u1_struct_0(X1))|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.47  cnf(c_0_81, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_54]), c_0_47])])).
% 0.20/0.47  cnf(c_0_82, negated_conjecture, (l1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_54]), c_0_47])])).
% 0.20/0.47  cnf(c_0_83, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~v2_pre_topc(X2)|~m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_65, c_0_77])).
% 0.20/0.47  cnf(c_0_84, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.47  cnf(c_0_85, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.47  cnf(c_0_86, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk2_0))|X1!=esk4_0|~m1_subset_1(X2,u1_struct_0(esk3_0))|X2!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.47  cnf(c_0_87, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))|m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])]), c_0_56])).
% 0.20/0.47  cnf(c_0_88, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_74]), c_0_75]), c_0_47])])).
% 0.20/0.47  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.47  cnf(c_0_90, negated_conjecture, (~m1_subset_1(esk4_0,u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_86])])).
% 0.20/0.47  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_87]), c_0_46]), c_0_54]), c_0_47])]), c_0_49]), c_0_56]), c_0_48])).
% 0.20/0.47  cnf(c_0_92, negated_conjecture, (m1_pre_topc(k2_tsep_1(esk1_0,esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_46])])).
% 0.20/0.47  cnf(c_0_93, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_46]), c_0_47])])).
% 0.20/0.47  cnf(c_0_94, negated_conjecture, (~m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.20/0.47  cnf(c_0_95, negated_conjecture, (v2_struct_0(k2_tsep_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_92]), c_0_93])]), c_0_49]), c_0_94])).
% 0.20/0.47  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_95]), c_0_46]), c_0_54]), c_0_47])]), c_0_49]), c_0_56]), c_0_48]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 97
% 0.20/0.47  # Proof object clause steps            : 58
% 0.20/0.47  # Proof object formula steps           : 39
% 0.20/0.47  # Proof object conjectures             : 34
% 0.20/0.47  # Proof object clause conjectures      : 31
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 30
% 0.20/0.47  # Proof object initial formulas used   : 19
% 0.20/0.47  # Proof object generating inferences   : 20
% 0.20/0.47  # Proof object simplifying inferences  : 73
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 19
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 33
% 0.20/0.47  # Removed in clause preprocessing      : 8
% 0.20/0.47  # Initial clauses in saturation        : 25
% 0.20/0.47  # Processed clauses                    : 517
% 0.20/0.47  # ...of these trivial                  : 2
% 0.20/0.47  # ...subsumed                          : 27
% 0.20/0.47  # ...remaining for further processing  : 488
% 0.20/0.47  # Other redundant clauses eliminated   : 3
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 2
% 0.20/0.47  # Backward-rewritten                   : 94
% 0.20/0.47  # Generated clauses                    : 2332
% 0.20/0.47  # ...of the previous two non-trivial   : 2252
% 0.20/0.47  # Contextual simplify-reflections      : 12
% 0.20/0.47  # Paramodulations                      : 2318
% 0.20/0.47  # Factorizations                       : 12
% 0.20/0.47  # Equation resolutions                 : 3
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 365
% 0.20/0.47  #    Positive orientable unit clauses  : 41
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 5
% 0.20/0.47  #    Non-unit-clauses                  : 319
% 0.20/0.47  # Current number of unprocessed clauses: 1784
% 0.20/0.47  # ...number of literals in the above   : 8496
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 129
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 71281
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 32323
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 39
% 0.20/0.47  # Unit Clause-clause subsumption calls : 537
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 30
% 0.20/0.47  # BW rewrite match successes           : 5
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 126713
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.120 s
% 0.20/0.47  # System time              : 0.009 s
% 0.20/0.47  # Total time               : 0.128 s
% 0.20/0.47  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
