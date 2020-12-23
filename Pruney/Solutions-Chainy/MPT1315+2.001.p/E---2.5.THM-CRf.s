%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:19 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 126 expanded)
%              Number of clauses        :   35 (  50 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 ( 619 expanded)
%              Number of equality atoms :   43 (  95 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t34_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v4_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(t43_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v4_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v4_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k3_xboole_0(X5,X6) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_12,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X7,X8] : k2_tarski(X7,X8) = k2_tarski(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X14) = k3_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( v4_pre_topc(X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                     => ( X4 = X2
                       => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_tops_2])).

cnf(c_0_18,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_pre_topc(esk7_0,esk5_0)
    & v4_pre_topc(esk6_0,esk5_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & esk8_0 = esk6_0
    & ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X20,X21,X22,X24,X26] :
      ( ( r1_tarski(k2_struct_0(X21),k2_struct_0(X20))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk1_3(X20,X21,X22),u1_pre_topc(X20))
        | ~ r2_hidden(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( X22 = k9_subset_1(u1_struct_0(X21),esk1_3(X20,X21,X22),k2_struct_0(X21))
        | ~ r2_hidden(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X24,u1_pre_topc(X20))
        | X22 != k9_subset_1(u1_struct_0(X21),X24,k2_struct_0(X21))
        | r2_hidden(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r1_tarski(k2_struct_0(X21),k2_struct_0(X20))
        | m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r2_hidden(X26,u1_pre_topc(X20))
        | esk2_2(X20,X21) != k9_subset_1(u1_struct_0(X21),X26,k2_struct_0(X21))
        | ~ r1_tarski(k2_struct_0(X21),k2_struct_0(X20))
        | m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( m1_subset_1(esk3_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))
        | ~ r1_tarski(k2_struct_0(X21),k2_struct_0(X20))
        | m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( r2_hidden(esk3_2(X20,X21),u1_pre_topc(X20))
        | r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))
        | ~ r1_tarski(k2_struct_0(X21),k2_struct_0(X20))
        | m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) )
      & ( esk2_2(X20,X21) = k9_subset_1(u1_struct_0(X21),esk3_2(X20,X21),k2_struct_0(X21))
        | r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))
        | ~ r1_tarski(k2_struct_0(X21),k2_struct_0(X20))
        | m1_pre_topc(X21,X20)
        | ~ l1_pre_topc(X21)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_28,plain,(
    ! [X17,X18,X19] :
      ( ( X19 != k1_pre_topc(X17,X18)
        | k2_struct_0(X19) = X18
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( k2_struct_0(X19) != X18
        | X19 = k1_pre_topc(X17,X18)
        | ~ v1_pre_topc(X19)
        | ~ m1_pre_topc(X19,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( ( v1_pre_topc(k1_pre_topc(X28,X29))
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) )
      & ( m1_pre_topc(k1_pre_topc(X28,X29),X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_30,plain,(
    ! [X32,X33,X34,X36] :
      ( ( m1_subset_1(esk4_3(X32,X33,X34),k1_zfmisc_1(u1_struct_0(X32)))
        | ~ v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X33,X32)
        | ~ l1_pre_topc(X32) )
      & ( v4_pre_topc(esk4_3(X32,X33,X34),X32)
        | ~ v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X33,X32)
        | ~ l1_pre_topc(X32) )
      & ( k9_subset_1(u1_struct_0(X33),esk4_3(X32,X33,X34),k2_struct_0(X33)) = X34
        | ~ v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X33,X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ v4_pre_topc(X36,X32)
        | k9_subset_1(u1_struct_0(X33),X36,k2_struct_0(X33)) != X34
        | v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X33,X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).

fof(c_0_31,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | k9_subset_1(X9,X10,X11) = k9_subset_1(X9,X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_32,plain,
    ( k9_subset_1(X1,X2,X3) = X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v4_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0) = esk6_0
    | ~ r1_tarski(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_45,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),esk6_0,X1) = esk6_0
    | ~ r1_tarski(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k2_struct_0(X2))
    | ~ m1_pre_topc(k1_pre_topc(X3,X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(esk6_0,k2_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_33])]),c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_49]),c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_33])])).

cnf(c_0_55,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_49]),c_0_50]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 12:34:41 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  # Version: 2.5pre002
% 0.13/0.36  # No SInE strategy applied
% 0.13/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.046 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.42  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.42  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.21/0.42  fof(t34_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 0.21/0.42  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.21/0.42  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.42  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.21/0.42  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.21/0.42  fof(t43_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v4_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_pre_topc)).
% 0.21/0.42  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.21/0.42  fof(c_0_11, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k3_xboole_0(X5,X6)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.42  fof(c_0_12, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.42  cnf(c_0_13, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.42  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.42  fof(c_0_15, plain, ![X7, X8]:k2_tarski(X7,X8)=k2_tarski(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.42  fof(c_0_16, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X14)=k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.21/0.42  fof(c_0_17, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3)))))))), inference(assume_negation,[status(cth)],[t34_tops_2])).
% 0.21/0.42  cnf(c_0_18, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.42  cnf(c_0_19, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.42  cnf(c_0_20, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  fof(c_0_21, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_pre_topc(esk7_0,esk5_0)&(v4_pre_topc(esk6_0,esk5_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))&(esk8_0=esk6_0&~v4_pre_topc(esk8_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.42  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.42  cnf(c_0_23, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_20, c_0_14])).
% 0.21/0.42  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_25, negated_conjecture, (esk8_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  fof(c_0_26, plain, ![X20, X21, X22, X24, X26]:(((r1_tarski(k2_struct_0(X21),k2_struct_0(X20))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20))&((((m1_subset_1(esk1_3(X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))|~r2_hidden(X22,u1_pre_topc(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(r2_hidden(esk1_3(X20,X21,X22),u1_pre_topc(X20))|~r2_hidden(X22,u1_pre_topc(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20)))&(X22=k9_subset_1(u1_struct_0(X21),esk1_3(X20,X21,X22),k2_struct_0(X21))|~r2_hidden(X22,u1_pre_topc(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20)))&(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X20)))|~r2_hidden(X24,u1_pre_topc(X20))|X22!=k9_subset_1(u1_struct_0(X21),X24,k2_struct_0(X21))|r2_hidden(X22,u1_pre_topc(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20))))&((m1_subset_1(esk2_2(X20,X21),k1_zfmisc_1(u1_struct_0(X21)))|~r1_tarski(k2_struct_0(X21),k2_struct_0(X20))|m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20))&((~r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X20)))|~r2_hidden(X26,u1_pre_topc(X20))|esk2_2(X20,X21)!=k9_subset_1(u1_struct_0(X21),X26,k2_struct_0(X21)))|~r1_tarski(k2_struct_0(X21),k2_struct_0(X20))|m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(((m1_subset_1(esk3_2(X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))|~r1_tarski(k2_struct_0(X21),k2_struct_0(X20))|m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20))&(r2_hidden(esk3_2(X20,X21),u1_pre_topc(X20))|r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))|~r1_tarski(k2_struct_0(X21),k2_struct_0(X20))|m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20)))&(esk2_2(X20,X21)=k9_subset_1(u1_struct_0(X21),esk3_2(X20,X21),k2_struct_0(X21))|r2_hidden(esk2_2(X20,X21),u1_pre_topc(X21))|~r1_tarski(k2_struct_0(X21),k2_struct_0(X20))|m1_pre_topc(X21,X20)|~l1_pre_topc(X21)|~l1_pre_topc(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.21/0.42  fof(c_0_27, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|l1_pre_topc(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.42  fof(c_0_28, plain, ![X17, X18, X19]:((X19!=k1_pre_topc(X17,X18)|k2_struct_0(X19)=X18|(~v1_pre_topc(X19)|~m1_pre_topc(X19,X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(k2_struct_0(X19)!=X18|X19=k1_pre_topc(X17,X18)|(~v1_pre_topc(X19)|~m1_pre_topc(X19,X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.21/0.42  fof(c_0_29, plain, ![X28, X29]:((v1_pre_topc(k1_pre_topc(X28,X29))|(~l1_pre_topc(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))))&(m1_pre_topc(k1_pre_topc(X28,X29),X28)|(~l1_pre_topc(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.21/0.42  fof(c_0_30, plain, ![X32, X33, X34, X36]:((((m1_subset_1(esk4_3(X32,X33,X34),k1_zfmisc_1(u1_struct_0(X32)))|~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32))&(v4_pre_topc(esk4_3(X32,X33,X34),X32)|~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32)))&(k9_subset_1(u1_struct_0(X33),esk4_3(X32,X33,X34),k2_struct_0(X33))=X34|~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32)))&(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X32)))|~v4_pre_topc(X36,X32)|k9_subset_1(u1_struct_0(X33),X36,k2_struct_0(X33))!=X34|v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).
% 0.21/0.42  fof(c_0_31, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|k9_subset_1(X9,X10,X11)=k9_subset_1(X9,X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.21/0.42  cnf(c_0_32, plain, (k9_subset_1(X1,X2,X3)=X3|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.42  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.42  cnf(c_0_34, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.42  cnf(c_0_35, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.42  cnf(c_0_36, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.42  cnf(c_0_37, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.42  cnf(c_0_38, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.42  cnf(c_0_39, plain, (v4_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.42  cnf(c_0_40, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.42  cnf(c_0_41, negated_conjecture, (k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0)=esk6_0|~r1_tarski(esk6_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.42  cnf(c_0_42, negated_conjecture, (~v4_pre_topc(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_43, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.42  cnf(c_0_44, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_37]), c_0_38])).
% 0.21/0.42  cnf(c_0_45, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_39])).
% 0.21/0.42  cnf(c_0_46, negated_conjecture, (k9_subset_1(u1_struct_0(esk7_0),esk6_0,X1)=esk6_0|~r1_tarski(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33])])).
% 0.21/0.42  cnf(c_0_47, negated_conjecture, (~v4_pre_topc(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_42, c_0_25])).
% 0.21/0.42  cnf(c_0_48, plain, (r1_tarski(X1,k2_struct_0(X2))|~m1_pre_topc(k1_pre_topc(X3,X1),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.42  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_51, negated_conjecture, (~v4_pre_topc(esk6_0,X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(esk6_0,k2_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_33])]), c_0_47])).
% 0.21/0.42  cnf(c_0_52, plain, (r1_tarski(X1,k2_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_48, c_0_38])).
% 0.21/0.42  cnf(c_0_53, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_49]), c_0_50])])).
% 0.21/0.42  cnf(c_0_54, negated_conjecture, (~v4_pre_topc(esk6_0,X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_33])])).
% 0.21/0.42  cnf(c_0_55, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_49]), c_0_50]), c_0_56])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 58
% 0.21/0.42  # Proof object clause steps            : 35
% 0.21/0.42  # Proof object formula steps           : 23
% 0.21/0.42  # Proof object conjectures             : 18
% 0.21/0.42  # Proof object clause conjectures      : 15
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 18
% 0.21/0.42  # Proof object initial formulas used   : 11
% 0.21/0.42  # Proof object generating inferences   : 10
% 0.21/0.42  # Proof object simplifying inferences  : 23
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 11
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 31
% 0.21/0.42  # Removed in clause preprocessing      : 1
% 0.21/0.42  # Initial clauses in saturation        : 30
% 0.21/0.42  # Processed clauses                    : 98
% 0.21/0.42  # ...of these trivial                  : 0
% 0.21/0.42  # ...subsumed                          : 15
% 0.21/0.42  # ...remaining for further processing  : 83
% 0.21/0.42  # Other redundant clauses eliminated   : 4
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 1
% 0.21/0.42  # Backward-rewritten                   : 0
% 0.21/0.42  # Generated clauses                    : 94
% 0.21/0.42  # ...of the previous two non-trivial   : 85
% 0.21/0.42  # Contextual simplify-reflections      : 8
% 0.21/0.42  # Paramodulations                      : 90
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 4
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 48
% 0.21/0.42  #    Positive orientable unit clauses  : 7
% 0.21/0.42  #    Positive unorientable unit clauses: 1
% 0.21/0.42  #    Negative unit clauses             : 1
% 0.21/0.42  #    Non-unit-clauses                  : 39
% 0.21/0.42  # Current number of unprocessed clauses: 47
% 0.21/0.42  # ...number of literals in the above   : 264
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 32
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 609
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 92
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 24
% 0.21/0.42  # Unit Clause-clause subsumption calls : 0
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 6
% 0.21/0.42  # BW rewrite match successes           : 4
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 5090
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.057 s
% 0.21/0.42  # System time              : 0.004 s
% 0.21/0.42  # Total time               : 0.061 s
% 0.21/0.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
