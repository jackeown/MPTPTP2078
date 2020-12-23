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
% DateTime   : Thu Dec  3 11:10:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 145 expanded)
%              Number of clauses        :   37 (  56 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 ( 425 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tops_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t42_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(t32_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => k7_subset_1(X1,X2,X3) = k9_subset_1(X1,X2,k3_subset_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(dt_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tops_1])).

fof(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | k4_subset_1(X24,X25,X26) = k2_xboole_0(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X11,X10)
      | r1_tarski(k2_xboole_0(X9,X11),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

fof(c_0_21,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(X33))
      | ~ m1_subset_1(X35,k1_zfmisc_1(X33))
      | r1_tarski(k3_subset_1(X33,X34),k3_subset_1(X33,k9_subset_1(X33,X34,X35))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_subset_1])])])).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | k3_subset_1(X22,k3_subset_1(X22,X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_23,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | m1_subset_1(k3_subset_1(X17,X18),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_24,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X14) = k9_subset_1(X12,X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

fof(c_0_25,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | ~ m1_subset_1(X32,k1_zfmisc_1(X30))
      | k7_subset_1(X30,X31,X32) = k9_subset_1(X30,X31,k3_subset_1(X30,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).

fof(c_0_26,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | k3_subset_1(X15,X16) = k4_xboole_0(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_27,plain,(
    ! [X4,X5,X6] : k4_xboole_0(k4_xboole_0(X4,X5),X6) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X38,X39,X40] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ r1_tarski(X39,X40)
      | r1_tarski(k1_tops_1(X38,X39),k1_tops_1(X38,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_31,plain,
    ( r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,k9_subset_1(X2,X1,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k7_subset_1(X2,X1,X3) = k9_subset_1(X2,X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k9_subset_1(X2,k3_subset_1(X2,X1),X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_43,plain,
    ( k9_subset_1(X1,k3_subset_1(X1,X2),X3) = k7_subset_1(X1,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_44,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | k7_subset_1(X27,X28,X29) = k4_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k3_subset_1(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_46,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | m1_subset_1(k4_subset_1(X19,X20,X21),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))
    | ~ r1_tarski(esk3_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k7_subset_1(X2,X3,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k3_subset_1(X1,k2_xboole_0(X2,X3)) = k4_xboole_0(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_52,plain,
    ( m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk3_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))
    | ~ r1_tarski(esk2_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_39]),c_0_40]),c_0_48])])).

fof(c_0_54,plain,(
    ! [X7,X8] : r1_tarski(X7,k2_xboole_0(X7,X8)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k4_xboole_0(X3,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( k3_subset_1(X1,k4_xboole_0(k3_subset_1(X1,X2),X3)) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_51])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk3_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))
    | ~ r1_tarski(esk2_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_52]),c_0_41]),c_0_48])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_19]),c_0_59]),c_0_41]),c_0_48])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_41])).

fof(c_0_63,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | m1_subset_1(k1_tops_1(X36,X37),k1_zfmisc_1(u1_struct_0(X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_48])])).

cnf(c_0_65,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_40]),c_0_41])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_65]),c_0_40]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 10:19:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t49_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tops_1)).
% 0.19/0.39  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.19/0.39  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.19/0.39  fof(t42_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,k9_subset_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 0.19/0.39  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.19/0.39  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.19/0.39  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.19/0.39  fof(t32_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k9_subset_1(X1,X2,k3_subset_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 0.19/0.39  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.19/0.39  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.19/0.39  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.39  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.39  fof(dt_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>m1_subset_1(k4_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 0.19/0.39  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.39  fof(dt_k1_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 0.19/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k4_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)),k1_tops_1(X1,k4_subset_1(u1_struct_0(X1),X2,X3))))))), inference(assume_negation,[status(cth)],[t49_tops_1])).
% 0.19/0.39  fof(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.39  fof(c_0_17, plain, ![X24, X25, X26]:(~m1_subset_1(X25,k1_zfmisc_1(X24))|~m1_subset_1(X26,k1_zfmisc_1(X24))|k4_subset_1(X24,X25,X26)=k2_xboole_0(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (~r1_tarski(k4_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_19, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  fof(c_0_20, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X11,X10)|r1_tarski(k2_xboole_0(X9,X11),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.19/0.39  fof(c_0_21, plain, ![X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(X33))|(~m1_subset_1(X35,k1_zfmisc_1(X33))|r1_tarski(k3_subset_1(X33,X34),k3_subset_1(X33,k9_subset_1(X33,X34,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t42_subset_1])])])).
% 0.19/0.39  fof(c_0_22, plain, ![X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|k3_subset_1(X22,k3_subset_1(X22,X23))=X23), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.19/0.39  fof(c_0_23, plain, ![X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|m1_subset_1(k3_subset_1(X17,X18),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.19/0.39  fof(c_0_24, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X14)=k9_subset_1(X12,X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.19/0.39  fof(c_0_25, plain, ![X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(X30))|(~m1_subset_1(X32,k1_zfmisc_1(X30))|k7_subset_1(X30,X31,X32)=k9_subset_1(X30,X31,k3_subset_1(X30,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_subset_1])])])).
% 0.19/0.39  fof(c_0_26, plain, ![X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|k3_subset_1(X15,X16)=k4_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.19/0.39  fof(c_0_27, plain, ![X4, X5, X6]:k4_xboole_0(k4_xboole_0(X4,X5),X6)=k4_xboole_0(X4,k2_xboole_0(X5,X6)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k2_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.39  cnf(c_0_29, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  fof(c_0_30, plain, ![X38, X39, X40]:(~l1_pre_topc(X38)|(~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|(~r1_tarski(X39,X40)|r1_tarski(k1_tops_1(X38,X39),k1_tops_1(X38,X40)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.39  cnf(c_0_31, plain, (r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,k9_subset_1(X2,X1,X3)))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_32, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_33, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_34, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_35, plain, (k7_subset_1(X2,X1,X3)=k9_subset_1(X2,X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_36, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_37, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk3_0),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.39  cnf(c_0_39, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_42, plain, (r1_tarski(X1,k3_subset_1(X2,k9_subset_1(X2,k3_subset_1(X2,X1),X3)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.39  cnf(c_0_43, plain, (k9_subset_1(X1,k3_subset_1(X1,X2),X3)=k7_subset_1(X1,X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.39  fof(c_0_44, plain, ![X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(X27))|k7_subset_1(X27,X28,X29)=k4_xboole_0(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.39  cnf(c_0_45, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k3_subset_1(X1,k2_xboole_0(X2,X3))|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.39  fof(c_0_46, plain, ![X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(X19))|~m1_subset_1(X21,k1_zfmisc_1(X19))|m1_subset_1(k4_subset_1(X19,X20,X21),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_subset_1])])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)))|~r1_tarski(esk3_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_49, plain, (r1_tarski(X1,k3_subset_1(X2,k7_subset_1(X2,X3,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.39  cnf(c_0_50, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.39  cnf(c_0_51, plain, (k3_subset_1(X1,k2_xboole_0(X2,X3))=k4_xboole_0(k3_subset_1(X1,X2),X3)|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 0.19/0.39  cnf(c_0_52, plain, (m1_subset_1(k4_subset_1(X2,X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (~m1_subset_1(k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk3_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))|~r1_tarski(esk2_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_39]), c_0_40]), c_0_48])])).
% 0.19/0.39  fof(c_0_54, plain, ![X7, X8]:r1_tarski(X7,k2_xboole_0(X7,X8)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.39  cnf(c_0_55, plain, (r1_tarski(X1,k3_subset_1(X2,k4_xboole_0(X3,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.39  cnf(c_0_56, plain, (k3_subset_1(X1,k4_xboole_0(k3_subset_1(X1,X2),X3))=k2_xboole_0(X2,X3)|~m1_subset_1(k2_xboole_0(X2,X3),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_51])).
% 0.19/0.39  cnf(c_0_57, plain, (m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_52, c_0_19])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk3_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))|~r1_tarski(esk2_0,k4_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_52]), c_0_41]), c_0_48])])).
% 0.19/0.39  cnf(c_0_59, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.39  cnf(c_0_60, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_33])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk3_0,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_19]), c_0_59]), c_0_41]), c_0_48])])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_60, c_0_41])).
% 0.19/0.39  fof(c_0_63, plain, ![X36, X37]:(~l1_pre_topc(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|m1_subset_1(k1_tops_1(X36,X37),k1_zfmisc_1(u1_struct_0(X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_48])])).
% 0.19/0.39  cnf(c_0_65, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_40]), c_0_41])])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_65]), c_0_40]), c_0_48])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 68
% 0.19/0.39  # Proof object clause steps            : 37
% 0.19/0.39  # Proof object formula steps           : 31
% 0.19/0.39  # Proof object conjectures             : 17
% 0.19/0.39  # Proof object clause conjectures      : 14
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 18
% 0.19/0.39  # Proof object initial formulas used   : 15
% 0.19/0.39  # Proof object generating inferences   : 19
% 0.19/0.39  # Proof object simplifying inferences  : 24
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 15
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 18
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 18
% 0.19/0.39  # Processed clauses                    : 129
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 27
% 0.19/0.39  # ...remaining for further processing  : 102
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 11
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 487
% 0.19/0.39  # ...of the previous two non-trivial   : 481
% 0.19/0.39  # Contextual simplify-reflections      : 14
% 0.19/0.39  # Paramodulations                      : 487
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
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
% 0.19/0.39  # Current number of processed clauses  : 73
% 0.19/0.39  #    Positive orientable unit clauses  : 5
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 65
% 0.19/0.39  # Current number of unprocessed clauses: 385
% 0.19/0.39  # ...number of literals in the above   : 1863
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 29
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1675
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 843
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 52
% 0.19/0.39  # Unit Clause-clause subsumption calls : 1
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 0
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 12715
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.039 s
% 0.19/0.39  # System time              : 0.008 s
% 0.19/0.39  # Total time               : 0.046 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
