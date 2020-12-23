%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:37 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 269 expanded)
%              Number of clauses        :   44 ( 111 expanded)
%              Number of leaves         :    9 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 ( 915 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_tex_2(X2,X1)
                  | v2_tex_2(X3,X1) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(t28_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r1_tarski(X3,X2)
                  & v2_tex_2(X2,X1) )
               => v2_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t33_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k3_subset_1(X1,k7_subset_1(X1,X2,X3)) = k4_subset_1(X1,k3_subset_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(t41_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v2_tex_2(X2,X1)
                    | v2_tex_2(X3,X1) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_tex_2])).

fof(c_0_10,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ r1_tarski(X25,X24)
      | ~ v2_tex_2(X24,X23)
      | v2_tex_2(X25,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( v2_tex_2(esk2_0,esk1_0)
      | v2_tex_2(esk3_0,esk1_0) )
    & ~ v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,k3_subset_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_15,plain,
    ( v2_tex_2(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ v2_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | k7_subset_1(X14,X15,X16) = k9_subset_1(X14,X15,k3_subset_1(X14,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v2_tex_2(X1,esk1_0)
    | ~ v2_tex_2(X2,esk1_0)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,plain,(
    ! [X4,X5,X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X4))
      | k9_subset_1(X4,X5,X6) = k9_subset_1(X4,X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

fof(c_0_25,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k3_subset_1(X17,k7_subset_1(X17,X18,X19)) = k4_subset_1(X17,k3_subset_1(X17,X18),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).

cnf(c_0_26,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk1_0)
    | ~ v2_tex_2(X2,esk1_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | r1_tarski(k3_subset_1(X20,k4_subset_1(X20,X21,X22)),k3_subset_1(X20,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).

cnf(c_0_33,plain,
    ( k3_subset_1(X2,k7_subset_1(X2,X1,X3)) = k4_subset_1(X2,k3_subset_1(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk1_0)
    | ~ v2_tex_2(esk2_0,esk1_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_37,plain,
    ( r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk1_0)
    | ~ v2_tex_2(esk2_0,esk1_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0))),k3_subset_1(u1_struct_0(esk1_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0))) = k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk1_0)
    | ~ v2_tex_2(esk3_0,esk1_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_44]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk1_0)
    | ~ v2_tex_2(esk3_0,esk1_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( v2_tex_2(esk2_0,esk1_0)
    | v2_tex_2(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_tex_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_55,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk3_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_18]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_tex_2(esk3_0,esk1_0)
    | ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( v2_tex_2(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k3_subset_1(u1_struct_0(esk1_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_60,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_18]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_27]),c_0_28]),c_0_60]),c_0_47]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:32:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.48/1.68  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 1.48/1.68  # and selection function SelectCQIAr.
% 1.48/1.68  #
% 1.48/1.68  # Preprocessing time       : 0.027 s
% 1.48/1.68  # Presaturation interreduction done
% 1.48/1.68  
% 1.48/1.68  # Proof found!
% 1.48/1.68  # SZS status Theorem
% 1.48/1.68  # SZS output start CNFRefutation
% 1.48/1.68  fof(t29_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tex_2)).
% 1.48/1.68  fof(t28_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r1_tarski(X3,X2)&v2_tex_2(X2,X1))=>v2_tex_2(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tex_2)).
% 1.48/1.68  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 1.48/1.68  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.48/1.68  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.48/1.68  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 1.48/1.68  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 1.48/1.68  fof(t33_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k3_subset_1(X1,k7_subset_1(X1,X2,X3))=k4_subset_1(X1,k3_subset_1(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 1.48/1.68  fof(t41_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X3)),k3_subset_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 1.48/1.68  fof(c_0_9, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v2_tex_2(X2,X1)|v2_tex_2(X3,X1))=>v2_tex_2(k9_subset_1(u1_struct_0(X1),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t29_tex_2])).
% 1.48/1.68  fof(c_0_10, plain, ![X23, X24, X25]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|(~r1_tarski(X25,X24)|~v2_tex_2(X24,X23)|v2_tex_2(X25,X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_tex_2])])])).
% 1.48/1.68  fof(c_0_11, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((v2_tex_2(esk2_0,esk1_0)|v2_tex_2(esk3_0,esk1_0))&~v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 1.48/1.68  fof(c_0_12, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 1.48/1.68  fof(c_0_13, plain, ![X7, X8]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|m1_subset_1(k3_subset_1(X7,X8),k1_zfmisc_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 1.48/1.68  fof(c_0_14, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,k3_subset_1(X12,X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 1.48/1.68  cnf(c_0_15, plain, (v2_tex_2(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~v2_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.48/1.68  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.48/1.68  cnf(c_0_17, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.48/1.68  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.48/1.68  fof(c_0_19, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|(~m1_subset_1(X16,k1_zfmisc_1(X14))|k7_subset_1(X14,X15,X16)=k9_subset_1(X14,X15,k3_subset_1(X14,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 1.48/1.68  cnf(c_0_20, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.48/1.68  cnf(c_0_21, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.48/1.68  cnf(c_0_22, negated_conjecture, (v2_tex_2(X1,esk1_0)|~v2_tex_2(X2,esk1_0)|~r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.48/1.68  cnf(c_0_23, negated_conjecture, (m1_subset_1(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 1.48/1.68  fof(c_0_24, plain, ![X4, X5, X6]:(~m1_subset_1(X6,k1_zfmisc_1(X4))|k9_subset_1(X4,X5,X6)=k9_subset_1(X4,X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 1.48/1.68  fof(c_0_25, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|(~m1_subset_1(X19,k1_zfmisc_1(X17))|k3_subset_1(X17,k7_subset_1(X17,X18,X19))=k4_subset_1(X17,k3_subset_1(X17,X18),X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_subset_1])])])).
% 1.48/1.68  cnf(c_0_26, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.48/1.68  cnf(c_0_27, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 1.48/1.68  cnf(c_0_28, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 1.48/1.68  cnf(c_0_29, negated_conjecture, (v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk1_0)|~v2_tex_2(X2,esk1_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.48/1.68  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.48/1.68  cnf(c_0_31, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.48/1.68  fof(c_0_32, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|(~m1_subset_1(X22,k1_zfmisc_1(X20))|r1_tarski(k3_subset_1(X20,k4_subset_1(X20,X21,X22)),k3_subset_1(X20,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_subset_1])])])).
% 1.48/1.68  cnf(c_0_33, plain, (k3_subset_1(X2,k7_subset_1(X2,X1,X3))=k4_subset_1(X2,k3_subset_1(X2,X1),X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.48/1.68  cnf(c_0_34, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0))=k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 1.48/1.68  cnf(c_0_35, negated_conjecture, (v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk1_0)|~v2_tex_2(esk2_0,esk1_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.48/1.68  cnf(c_0_36, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1)=k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 1.48/1.68  cnf(c_0_37, plain, (r1_tarski(k3_subset_1(X2,k4_subset_1(X2,X1,X3)),k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.48/1.68  cnf(c_0_38, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk3_0))=k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_33, c_0_27])).
% 1.48/1.68  cnf(c_0_39, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk3_0))=k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_30])).
% 1.48/1.68  cnf(c_0_40, negated_conjecture, (v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk1_0)|~v2_tex_2(esk2_0,esk1_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.48/1.68  cnf(c_0_41, negated_conjecture, (k9_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 1.48/1.68  cnf(c_0_42, negated_conjecture, (~v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.48/1.68  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk3_0))),k3_subset_1(u1_struct_0(esk1_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 1.48/1.68  cnf(c_0_44, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_20, c_0_30])).
% 1.48/1.68  cnf(c_0_45, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_21, c_0_30])).
% 1.48/1.68  cnf(c_0_46, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0))=k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_30]), c_0_39])).
% 1.48/1.68  cnf(c_0_47, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0)))=k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 1.48/1.68  cnf(c_0_48, negated_conjecture, (v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk1_0)|~v2_tex_2(esk3_0,esk1_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),X1,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_18])).
% 1.48/1.68  cnf(c_0_49, negated_conjecture, (~v2_tex_2(esk2_0,esk1_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 1.48/1.68  cnf(c_0_50, negated_conjecture, (r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 1.48/1.68  cnf(c_0_51, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(u1_struct_0(esk1_0),X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_44]), c_0_45])).
% 1.48/1.68  cnf(c_0_52, negated_conjecture, (v2_tex_2(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk1_0)|~v2_tex_2(esk3_0,esk1_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk3_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_36])).
% 1.48/1.68  cnf(c_0_53, negated_conjecture, (v2_tex_2(esk2_0,esk1_0)|v2_tex_2(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.48/1.68  cnf(c_0_54, negated_conjecture, (~v2_tex_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 1.48/1.68  cnf(c_0_55, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),X1),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k7_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_33, c_0_44])).
% 1.48/1.68  cnf(c_0_56, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk3_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_18]), c_0_36])).
% 1.48/1.68  cnf(c_0_57, negated_conjecture, (~v2_tex_2(esk3_0,esk1_0)|~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_42])).
% 1.48/1.68  cnf(c_0_58, negated_conjecture, (v2_tex_2(esk3_0,esk1_0)), inference(sr,[status(thm)],[c_0_53, c_0_54])).
% 1.48/1.68  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k4_subset_1(u1_struct_0(esk1_0),X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))),k3_subset_1(u1_struct_0(esk1_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_37, c_0_44])).
% 1.48/1.68  cnf(c_0_60, negated_conjecture, (k4_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk3_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_18]), c_0_56])).
% 1.48/1.68  cnf(c_0_61, negated_conjecture, (~r1_tarski(k9_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 1.48/1.68  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_27]), c_0_28]), c_0_60]), c_0_47]), c_0_61]), ['proof']).
% 1.48/1.68  # SZS output end CNFRefutation
% 1.48/1.68  # Proof object total steps             : 63
% 1.48/1.68  # Proof object clause steps            : 44
% 1.48/1.68  # Proof object formula steps           : 19
% 1.48/1.68  # Proof object conjectures             : 39
% 1.48/1.68  # Proof object clause conjectures      : 36
% 1.48/1.68  # Proof object formula conjectures     : 3
% 1.48/1.68  # Proof object initial clauses used    : 13
% 1.48/1.68  # Proof object initial formulas used   : 9
% 1.48/1.68  # Proof object generating inferences   : 28
% 1.48/1.68  # Proof object simplifying inferences  : 19
% 1.48/1.68  # Training examples: 0 positive, 0 negative
% 1.48/1.68  # Parsed axioms                        : 9
% 1.48/1.68  # Removed by relevancy pruning/SinE    : 0
% 1.48/1.68  # Initial clauses                      : 13
% 1.48/1.68  # Removed in clause preprocessing      : 0
% 1.48/1.68  # Initial clauses in saturation        : 13
% 1.48/1.68  # Processed clauses                    : 6695
% 1.48/1.68  # ...of these trivial                  : 1029
% 1.48/1.68  # ...subsumed                          : 3436
% 1.48/1.68  # ...remaining for further processing  : 2229
% 1.48/1.68  # Other redundant clauses eliminated   : 0
% 1.48/1.68  # Clauses deleted for lack of memory   : 0
% 1.48/1.68  # Backward-subsumed                    : 33
% 1.48/1.68  # Backward-rewritten                   : 421
% 1.48/1.68  # Generated clauses                    : 145488
% 1.48/1.68  # ...of the previous two non-trivial   : 132771
% 1.48/1.68  # Contextual simplify-reflections      : 2
% 1.48/1.68  # Paramodulations                      : 145484
% 1.48/1.68  # Factorizations                       : 0
% 1.48/1.68  # Equation resolutions                 : 0
% 1.48/1.68  # Propositional unsat checks           : 0
% 1.48/1.68  #    Propositional check models        : 0
% 1.48/1.68  #    Propositional check unsatisfiable : 0
% 1.48/1.68  #    Propositional clauses             : 0
% 1.48/1.68  #    Propositional clauses after purity: 0
% 1.48/1.68  #    Propositional unsat core size     : 0
% 1.48/1.68  #    Propositional preprocessing time  : 0.000
% 1.48/1.68  #    Propositional encoding time       : 0.000
% 1.48/1.68  #    Propositional solver time         : 0.000
% 1.48/1.68  #    Success case prop preproc time    : 0.000
% 1.48/1.68  #    Success case prop encoding time   : 0.000
% 1.48/1.68  #    Success case prop solver time     : 0.000
% 1.48/1.68  # Current number of processed clauses  : 1758
% 1.48/1.68  #    Positive orientable unit clauses  : 855
% 1.48/1.68  #    Positive unorientable unit clauses: 32
% 1.48/1.68  #    Negative unit clauses             : 7
% 1.48/1.68  #    Non-unit-clauses                  : 864
% 1.48/1.68  # Current number of unprocessed clauses: 125890
% 1.48/1.68  # ...number of literals in the above   : 205743
% 1.48/1.68  # Current number of archived formulas  : 0
% 1.48/1.68  # Current number of archived clauses   : 471
% 1.48/1.68  # Clause-clause subsumption calls (NU) : 372402
% 1.48/1.68  # Rec. Clause-clause subsumption calls : 329013
% 1.48/1.68  # Non-unit clause-clause subsumptions  : 3402
% 1.48/1.68  # Unit Clause-clause subsumption calls : 5156
% 1.48/1.68  # Rewrite failures with RHS unbound    : 0
% 1.48/1.68  # BW rewrite match attempts            : 43057
% 1.48/1.68  # BW rewrite match successes           : 280
% 1.48/1.68  # Condensation attempts                : 0
% 1.48/1.68  # Condensation successes               : 0
% 1.48/1.68  # Termbank termtop insertions          : 5579690
% 1.48/1.69  
% 1.48/1.69  # -------------------------------------------------
% 1.48/1.69  # User time                : 1.275 s
% 1.48/1.69  # System time              : 0.075 s
% 1.48/1.69  # Total time               : 1.350 s
% 1.48/1.69  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
