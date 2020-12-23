%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 341 expanded)
%              Number of clauses        :   43 ( 130 expanded)
%              Number of leaves         :   16 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 ( 935 expanded)
%              Number of equality atoms :   30 ( 212 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(t20_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v8_pre_topc(X1)
                  & v2_compts_1(X2,X1)
                  & v2_compts_1(X3,X1) )
               => v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t18_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_compts_1(X2,X1)
                  & r1_tarski(X3,X2)
                  & v4_pre_topc(X3,X1) )
               => v2_compts_1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fc4_tops_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & v4_pre_topc(X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & v4_pre_topc(X3,X1)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => v4_pre_topc(k3_xboole_0(X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

fof(t16_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v8_pre_topc(X1)
              & v2_compts_1(X2,X1) )
           => v4_pre_topc(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

fof(c_0_16,plain,(
    ! [X43,X44] : k1_setfam_1(k2_tarski(X43,X44)) = k3_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_17,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X40))
      | k9_subset_1(X40,X41,X42) = k3_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X13,X14,X15,X16] : k3_enumset1(X13,X13,X14,X15,X16) = k2_enumset1(X13,X14,X15,X16) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X17,X18,X19,X20,X21] : k4_enumset1(X17,X17,X18,X19,X20,X21) = k3_enumset1(X17,X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_24,plain,(
    ! [X22,X23,X24,X25,X26,X27] : k5_enumset1(X22,X22,X23,X24,X25,X26,X27) = k4_enumset1(X22,X23,X24,X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_25,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34] : k6_enumset1(X28,X28,X29,X30,X31,X32,X33,X34) = k5_enumset1(X28,X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_33,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | m1_subset_1(k9_subset_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_34,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_35,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_34])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v8_pre_topc(X1)
                    & v2_compts_1(X2,X1)
                    & v2_compts_1(X3,X1) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_compts_1])).

cnf(c_0_38,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v8_pre_topc(esk1_0)
    & v2_compts_1(esk2_0,esk1_0)
    & v2_compts_1(esk3_0,esk1_0)
    & ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

fof(c_0_40,plain,(
    ! [X36] : m1_subset_1(k2_subset_1(X36),k1_zfmisc_1(X36)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_41,plain,(
    ! [X35] : k2_subset_1(X35) = X35 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_48,plain,(
    ! [X52,X53,X54] :
      ( ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ v2_compts_1(X53,X52)
      | ~ r1_tarski(X54,X53)
      | ~ v4_pre_topc(X54,X52)
      | v2_compts_1(X54,X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_compts_1(X2,X1)
    | ~ r1_tarski(X3,X2)
    | ~ v4_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k9_subset_1(X1,X2,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_54,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X45,k1_zfmisc_1(X46))
        | r1_tarski(X45,X46) )
      & ( ~ r1_tarski(X45,X46)
        | m1_subset_1(X45,k1_zfmisc_1(X46)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_55,plain,(
    ! [X47,X48,X49] :
      ( ~ v2_pre_topc(X47)
      | ~ l1_pre_topc(X47)
      | ~ v4_pre_topc(X48,X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))
      | ~ v4_pre_topc(X49,X47)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))
      | v4_pre_topc(k3_xboole_0(X48,X49),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_tops_1])])).

cnf(c_0_56,negated_conjecture,
    ( v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)
    | ~ v2_compts_1(X3,esk1_0)
    | ~ v4_pre_topc(k9_subset_1(X1,X2,esk3_0),esk1_0)
    | ~ r1_tarski(k9_subset_1(X1,X2,esk3_0),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,plain,
    ( v4_pre_topc(k3_xboole_0(X2,X3),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_59,plain,(
    ! [X50,X51] :
      ( ~ v2_pre_topc(X50)
      | ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | ~ v8_pre_topc(X50)
      | ~ v2_compts_1(X51,X50)
      | v4_pre_topc(X51,X50) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).

cnf(c_0_60,negated_conjecture,
    ( v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)
    | ~ v2_compts_1(X3,esk1_0)
    | ~ v4_pre_topc(k9_subset_1(X1,X2,esk3_0),esk1_0)
    | ~ m1_subset_1(k9_subset_1(X1,X2,esk3_0),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,plain,
    ( v4_pre_topc(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v4_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_62,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v8_pre_topc(X1)
    | ~ v2_compts_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v2_compts_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( v8_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_66,negated_conjecture,
    ( v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)
    | ~ v2_compts_1(X1,esk1_0)
    | ~ v4_pre_topc(k9_subset_1(X1,X2,esk3_0),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_35])).

cnf(c_0_67,plain,
    ( v4_pre_topc(k9_subset_1(X1,X2,X3),X4)
    | ~ v4_pre_topc(X3,X4)
    | ~ v4_pre_topc(X2,X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( v4_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_43]),c_0_63]),c_0_64]),c_0_52]),c_0_53])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_70,negated_conjecture,
    ( v2_compts_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_71,negated_conjecture,
    ( ~ v2_compts_1(k9_subset_1(X1,esk2_0,esk3_0),esk1_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_36]),c_0_43])])).

cnf(c_0_72,negated_conjecture,
    ( v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)
    | ~ v2_compts_1(X1,esk1_0)
    | ~ v4_pre_topc(X2,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_52]),c_0_53]),c_0_43])])).

cnf(c_0_73,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_69]),c_0_70]),c_0_64]),c_0_52]),c_0_53])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_compts_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_43]),c_0_63]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:29:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.019 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.37  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.20/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.37  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.20/0.37  fof(t20_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 0.20/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.37  fof(t18_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 0.20/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.37  fof(fc4_tops_1, axiom, ![X1, X2, X3]:((((((v2_pre_topc(X1)&l1_pre_topc(X1))&v4_pre_topc(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&v4_pre_topc(X3,X1))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>v4_pre_topc(k3_xboole_0(X2,X3),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 0.20/0.37  fof(t16_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v8_pre_topc(X1)&v2_compts_1(X2,X1))=>v4_pre_topc(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 0.20/0.37  fof(c_0_16, plain, ![X43, X44]:k1_setfam_1(k2_tarski(X43,X44))=k3_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.37  fof(c_0_17, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.37  fof(c_0_18, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X40))|k9_subset_1(X40,X41,X42)=k3_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.20/0.37  cnf(c_0_19, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.37  fof(c_0_21, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.37  fof(c_0_22, plain, ![X13, X14, X15, X16]:k3_enumset1(X13,X13,X14,X15,X16)=k2_enumset1(X13,X14,X15,X16), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.37  fof(c_0_23, plain, ![X17, X18, X19, X20, X21]:k4_enumset1(X17,X17,X18,X19,X20,X21)=k3_enumset1(X17,X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.37  fof(c_0_24, plain, ![X22, X23, X24, X25, X26, X27]:k5_enumset1(X22,X22,X23,X24,X25,X26,X27)=k4_enumset1(X22,X23,X24,X25,X26,X27), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.37  fof(c_0_25, plain, ![X28, X29, X30, X31, X32, X33, X34]:k6_enumset1(X28,X28,X29,X30,X31,X32,X33,X34)=k5_enumset1(X28,X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.37  cnf(c_0_26, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  cnf(c_0_27, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.37  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.37  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.37  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.37  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  fof(c_0_33, plain, ![X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(X37))|m1_subset_1(k9_subset_1(X37,X38,X39),k1_zfmisc_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.20/0.37  cnf(c_0_34, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.37  cnf(c_0_35, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.37  cnf(c_0_36, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_34, c_0_34])).
% 0.20/0.37  fof(c_0_37, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v8_pre_topc(X1)&v2_compts_1(X2,X1))&v2_compts_1(X3,X1))=>v2_compts_1(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t20_compts_1])).
% 0.20/0.37  cnf(c_0_38, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.37  fof(c_0_39, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(((v8_pre_topc(esk1_0)&v2_compts_1(esk2_0,esk1_0))&v2_compts_1(esk3_0,esk1_0))&~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.20/0.37  fof(c_0_40, plain, ![X36]:m1_subset_1(k2_subset_1(X36),k1_zfmisc_1(X36)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.37  fof(c_0_41, plain, ![X35]:k2_subset_1(X35)=X35, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.37  cnf(c_0_42, plain, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.20/0.37  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_44, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.37  cnf(c_0_45, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.37  cnf(c_0_46, negated_conjecture, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.37  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.37  fof(c_0_48, plain, ![X52, X53, X54]:(~v2_pre_topc(X52)|~l1_pre_topc(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|(~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X52)))|(~v2_compts_1(X53,X52)|~r1_tarski(X54,X53)|~v4_pre_topc(X54,X52)|v2_compts_1(X54,X52))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_compts_1])])])).
% 0.20/0.37  cnf(c_0_49, negated_conjecture, (m1_subset_1(k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.37  cnf(c_0_50, plain, (v2_compts_1(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_compts_1(X2,X1)|~r1_tarski(X3,X2)|~v4_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.37  cnf(c_0_51, negated_conjecture, (m1_subset_1(k9_subset_1(X1,X2,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_34])).
% 0.20/0.37  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_53, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  fof(c_0_54, plain, ![X45, X46]:((~m1_subset_1(X45,k1_zfmisc_1(X46))|r1_tarski(X45,X46))&(~r1_tarski(X45,X46)|m1_subset_1(X45,k1_zfmisc_1(X46)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.37  fof(c_0_55, plain, ![X47, X48, X49]:(~v2_pre_topc(X47)|~l1_pre_topc(X47)|~v4_pre_topc(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X47)))|~v4_pre_topc(X49,X47)|~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X47)))|v4_pre_topc(k3_xboole_0(X48,X49),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_tops_1])])).
% 0.20/0.37  cnf(c_0_56, negated_conjecture, (v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)|~v2_compts_1(X3,esk1_0)|~v4_pre_topc(k9_subset_1(X1,X2,esk3_0),esk1_0)|~r1_tarski(k9_subset_1(X1,X2,esk3_0),X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.20/0.37  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.37  cnf(c_0_58, plain, (v4_pre_topc(k3_xboole_0(X2,X3),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.37  fof(c_0_59, plain, ![X50, X51]:(~v2_pre_topc(X50)|~l1_pre_topc(X50)|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|(~v8_pre_topc(X50)|~v2_compts_1(X51,X50)|v4_pre_topc(X51,X50)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_compts_1])])])).
% 0.20/0.37  cnf(c_0_60, negated_conjecture, (v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)|~v2_compts_1(X3,esk1_0)|~v4_pre_topc(k9_subset_1(X1,X2,esk3_0),esk1_0)|~m1_subset_1(k9_subset_1(X1,X2,esk3_0),k1_zfmisc_1(X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.37  cnf(c_0_61, plain, (v4_pre_topc(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v4_pre_topc(X3,X1)|~v4_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.37  cnf(c_0_62, plain, (v4_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v8_pre_topc(X1)|~v2_compts_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.37  cnf(c_0_63, negated_conjecture, (v2_compts_1(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_64, negated_conjecture, (v8_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_65, negated_conjecture, (~v2_compts_1(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_66, negated_conjecture, (v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)|~v2_compts_1(X1,esk1_0)|~v4_pre_topc(k9_subset_1(X1,X2,esk3_0),esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_35])).
% 0.20/0.37  cnf(c_0_67, plain, (v4_pre_topc(k9_subset_1(X1,X2,X3),X4)|~v4_pre_topc(X3,X4)|~v4_pre_topc(X2,X4)|~l1_pre_topc(X4)|~v2_pre_topc(X4)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 0.20/0.37  cnf(c_0_68, negated_conjecture, (v4_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_43]), c_0_63]), c_0_64]), c_0_52]), c_0_53])])).
% 0.20/0.37  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_70, negated_conjecture, (v2_compts_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_71, negated_conjecture, (~v2_compts_1(k9_subset_1(X1,esk2_0,esk3_0),esk1_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_36]), c_0_43])])).
% 0.20/0.37  cnf(c_0_72, negated_conjecture, (v2_compts_1(k9_subset_1(X1,X2,esk3_0),esk1_0)|~v2_compts_1(X1,esk1_0)|~v4_pre_topc(X2,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_52]), c_0_53]), c_0_43])])).
% 0.20/0.37  cnf(c_0_73, negated_conjecture, (v4_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_69]), c_0_70]), c_0_64]), c_0_52]), c_0_53])])).
% 0.20/0.37  cnf(c_0_74, negated_conjecture, (~v2_compts_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_69])])).
% 0.20/0.37  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_43]), c_0_63]), c_0_47])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 76
% 0.20/0.37  # Proof object clause steps            : 43
% 0.20/0.37  # Proof object formula steps           : 33
% 0.20/0.37  # Proof object conjectures             : 23
% 0.20/0.37  # Proof object clause conjectures      : 20
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 23
% 0.20/0.37  # Proof object initial formulas used   : 16
% 0.20/0.37  # Proof object generating inferences   : 16
% 0.20/0.37  # Proof object simplifying inferences  : 40
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 16
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 24
% 0.20/0.37  # Removed in clause preprocessing      : 8
% 0.20/0.37  # Initial clauses in saturation        : 16
% 0.20/0.37  # Processed clauses                    : 114
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 41
% 0.20/0.37  # ...remaining for further processing  : 73
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 3
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 164
% 0.20/0.37  # ...of the previous two non-trivial   : 135
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 164
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 52
% 0.20/0.37  #    Positive orientable unit clauses  : 12
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 38
% 0.20/0.37  # Current number of unprocessed clauses: 50
% 0.20/0.37  # ...number of literals in the above   : 316
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 29
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 1180
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 254
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 40
% 0.20/0.37  # Unit Clause-clause subsumption calls : 11
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 4
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 6094
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.021 s
% 0.20/0.37  # System time              : 0.006 s
% 0.20/0.37  # Total time               : 0.028 s
% 0.20/0.37  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
