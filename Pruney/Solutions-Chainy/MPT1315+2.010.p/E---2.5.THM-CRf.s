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
% DateTime   : Thu Dec  3 11:13:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 246 expanded)
%              Number of clauses        :   44 ( 100 expanded)
%              Number of leaves         :   12 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  233 ( 955 expanded)
%              Number of equality atoms :   39 ( 172 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

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

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | l1_pre_topc(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_pre_topc(esk7_0,esk5_0)
    & v4_pre_topc(esk6_0,esk5_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & esk8_0 = esk6_0
    & ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_16,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X25,X27] :
      ( ( r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk1_3(X21,X22,X23),u1_pre_topc(X21))
        | ~ r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( X23 = k9_subset_1(u1_struct_0(X22),esk1_3(X21,X22,X23),k2_struct_0(X22))
        | ~ r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X25,u1_pre_topc(X21))
        | X23 != k9_subset_1(u1_struct_0(X22),X25,k2_struct_0(X22))
        | r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk2_2(X21,X22),k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( ~ r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X27,u1_pre_topc(X21))
        | esk2_2(X21,X22) != k9_subset_1(u1_struct_0(X22),X27,k2_struct_0(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk3_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk3_2(X21,X22),u1_pre_topc(X21))
        | r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) )
      & ( esk2_2(X21,X22) = k9_subset_1(u1_struct_0(X22),esk3_2(X21,X22),k2_struct_0(X22))
        | r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))
        | ~ r1_tarski(k2_struct_0(X22),k2_struct_0(X21))
        | m1_pre_topc(X22,X21)
        | ~ l1_pre_topc(X22)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_20,plain,(
    ! [X20] :
      ( ~ l1_struct_0(X20)
      | k2_struct_0(X20) = u1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_23,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X15) = k3_xboole_0(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_24,plain,(
    ! [X16,X17] : k1_setfam_1(k2_tarski(X16,X17)) = k3_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_29,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ~ r1_tarski(X5,X6)
      | k3_xboole_0(X5,X6) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_34,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( k2_struct_0(esk7_0) = u1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( k2_struct_0(esk5_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

cnf(c_0_38,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | m1_subset_1(k9_subset_1(X10,X11,X12),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_36]),c_0_37]),c_0_18])])).

fof(c_0_45,plain,(
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

fof(c_0_46,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | k9_subset_1(X7,X8,X9) = k9_subset_1(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,esk6_0)) = k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_53,plain,
    ( v4_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0) = k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_47]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_39])).

cnf(c_0_57,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk6_0,u1_struct_0(esk7_0))) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k1_setfam_1(k2_tarski(X1,u1_struct_0(esk7_0))) = k9_subset_1(u1_struct_0(esk5_0),X1,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ v4_pre_topc(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk7_0),esk6_0,X1) = k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_39]),c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1) = k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),esk6_0,u1_struct_0(esk7_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( ~ v4_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_36]),c_0_36]),c_0_62])]),c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_47]),c_0_67]),c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.21/0.38  # and selection function SelectComplexG.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.029 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t34_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 0.21/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.38  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.21/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.21/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.38  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.21/0.38  fof(t43_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v4_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_pre_topc)).
% 0.21/0.38  fof(commutativity_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k9_subset_1(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 0.21/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3)))))))), inference(assume_negation,[status(cth)],[t34_tops_2])).
% 0.21/0.38  fof(c_0_13, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|l1_pre_topc(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.38  fof(c_0_14, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_pre_topc(esk7_0,esk5_0)&(v4_pre_topc(esk6_0,esk5_0)&(m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))&(esk8_0=esk6_0&~v4_pre_topc(esk8_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.21/0.38  fof(c_0_15, plain, ![X29]:(~l1_pre_topc(X29)|l1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.38  cnf(c_0_16, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  fof(c_0_19, plain, ![X21, X22, X23, X25, X27]:(((r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&((((m1_subset_1(esk1_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(r2_hidden(esk1_3(X21,X22,X23),u1_pre_topc(X21))|~r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(X23=k9_subset_1(u1_struct_0(X22),esk1_3(X21,X22,X23),k2_struct_0(X22))|~r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X25,u1_pre_topc(X21))|X23!=k9_subset_1(u1_struct_0(X22),X25,k2_struct_0(X22))|r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))))&((m1_subset_1(esk2_2(X21,X22),k1_zfmisc_1(u1_struct_0(X22)))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&((~r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X21)))|~r2_hidden(X27,u1_pre_topc(X21))|esk2_2(X21,X22)!=k9_subset_1(u1_struct_0(X22),X27,k2_struct_0(X22)))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(((m1_subset_1(esk3_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))|r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21))&(r2_hidden(esk3_2(X21,X22),u1_pre_topc(X21))|r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))&(esk2_2(X21,X22)=k9_subset_1(u1_struct_0(X22),esk3_2(X21,X22),k2_struct_0(X22))|r2_hidden(esk2_2(X21,X22),u1_pre_topc(X22))|~r1_tarski(k2_struct_0(X22),k2_struct_0(X21))|m1_pre_topc(X22,X21)|~l1_pre_topc(X22)|~l1_pre_topc(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.21/0.38  fof(c_0_20, plain, ![X20]:(~l1_struct_0(X20)|k2_struct_0(X20)=u1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.38  cnf(c_0_21, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.21/0.38  fof(c_0_23, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X13))|k9_subset_1(X13,X14,X15)=k3_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.21/0.38  fof(c_0_24, plain, ![X16, X17]:k1_setfam_1(k2_tarski(X16,X17))=k3_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.38  cnf(c_0_25, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_26, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.38  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.21/0.38  cnf(c_0_29, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.38  cnf(c_0_30, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (esk8_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  fof(c_0_33, plain, ![X5, X6]:(~r1_tarski(X5,X6)|k3_xboole_0(X5,X6)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.38  fof(c_0_34, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.38  cnf(c_0_35, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_25, c_0_16])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, (k2_struct_0(esk7_0)=u1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.38  cnf(c_0_37, negated_conjecture, (k2_struct_0(esk5_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 0.21/0.38  cnf(c_0_38, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.38  fof(c_0_40, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|m1_subset_1(k9_subset_1(X10,X11,X12),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.21/0.38  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.38  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_17]), c_0_36]), c_0_37]), c_0_18])])).
% 0.21/0.38  fof(c_0_45, plain, ![X32, X33, X34, X36]:((((m1_subset_1(esk4_3(X32,X33,X34),k1_zfmisc_1(u1_struct_0(X32)))|~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32))&(v4_pre_topc(esk4_3(X32,X33,X34),X32)|~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32)))&(k9_subset_1(u1_struct_0(X33),esk4_3(X32,X33,X34),k2_struct_0(X33))=X34|~v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32)))&(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X32)))|~v4_pre_topc(X36,X32)|k9_subset_1(u1_struct_0(X33),X36,k2_struct_0(X33))!=X34|v4_pre_topc(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X33,X32)|~l1_pre_topc(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).
% 0.21/0.38  fof(c_0_46, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(X7))|k9_subset_1(X7,X8,X9)=k9_subset_1(X7,X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_48, negated_conjecture, (k1_setfam_1(k2_tarski(X1,esk6_0))=k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.38  cnf(c_0_49, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.38  cnf(c_0_50, plain, (k1_setfam_1(k2_tarski(X1,X2))=X1|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_41, c_0_30])).
% 0.21/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_39])).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.38  cnf(c_0_53, plain, (v4_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.38  cnf(c_0_54, plain, (k9_subset_1(X2,X3,X1)=k9_subset_1(X2,X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0)=k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_47]), c_0_48])).
% 0.21/0.38  cnf(c_0_56, negated_conjecture, (m1_subset_1(k9_subset_1(u1_struct_0(esk7_0),X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(spm,[status(thm)],[c_0_49, c_0_39])).
% 0.21/0.38  cnf(c_0_57, negated_conjecture, (k1_setfam_1(k2_tarski(esk6_0,u1_struct_0(esk7_0)))=esk6_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.38  cnf(c_0_58, negated_conjecture, (k1_setfam_1(k2_tarski(X1,u1_struct_0(esk7_0)))=k9_subset_1(u1_struct_0(esk5_0),X1,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_38, c_0_52])).
% 0.21/0.38  cnf(c_0_59, negated_conjecture, (~v4_pre_topc(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_60, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_53])).
% 0.21/0.38  cnf(c_0_61, negated_conjecture, (k9_subset_1(u1_struct_0(esk7_0),esk6_0,X1)=k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_39]), c_0_55])).
% 0.21/0.38  cnf(c_0_62, negated_conjecture, (m1_subset_1(k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(rw,[status(thm)],[c_0_56, c_0_55])).
% 0.21/0.38  cnf(c_0_63, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk6_0,X1)=k9_subset_1(u1_struct_0(esk5_0),X1,esk6_0)), inference(spm,[status(thm)],[c_0_54, c_0_47])).
% 0.21/0.38  cnf(c_0_64, negated_conjecture, (k9_subset_1(u1_struct_0(esk5_0),esk6_0,u1_struct_0(esk7_0))=esk6_0), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.38  cnf(c_0_65, negated_conjecture, (~v4_pre_topc(esk6_0,esk7_0)), inference(rw,[status(thm)],[c_0_59, c_0_32])).
% 0.21/0.38  cnf(c_0_66, negated_conjecture, (~v4_pre_topc(esk6_0,X1)|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_36]), c_0_36]), c_0_62])]), c_0_63]), c_0_64]), c_0_65])).
% 0.21/0.38  cnf(c_0_67, negated_conjecture, (v4_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_47]), c_0_67]), c_0_17]), c_0_18])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 69
% 0.21/0.38  # Proof object clause steps            : 44
% 0.21/0.38  # Proof object formula steps           : 25
% 0.21/0.38  # Proof object conjectures             : 31
% 0.21/0.38  # Proof object clause conjectures      : 28
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 19
% 0.21/0.38  # Proof object initial formulas used   : 12
% 0.21/0.38  # Proof object generating inferences   : 17
% 0.21/0.38  # Proof object simplifying inferences  : 27
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 12
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 31
% 0.21/0.38  # Removed in clause preprocessing      : 1
% 0.21/0.38  # Initial clauses in saturation        : 30
% 0.21/0.38  # Processed clauses                    : 112
% 0.21/0.38  # ...of these trivial                  : 2
% 0.21/0.38  # ...subsumed                          : 3
% 0.21/0.38  # ...remaining for further processing  : 107
% 0.21/0.38  # Other redundant clauses eliminated   : 2
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 3
% 0.21/0.38  # Generated clauses                    : 164
% 0.21/0.38  # ...of the previous two non-trivial   : 139
% 0.21/0.38  # Contextual simplify-reflections      : 5
% 0.21/0.38  # Paramodulations                      : 162
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 2
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 72
% 0.21/0.38  #    Positive orientable unit clauses  : 32
% 0.21/0.38  #    Positive unorientable unit clauses: 1
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 38
% 0.21/0.38  # Current number of unprocessed clauses: 85
% 0.21/0.38  # ...number of literals in the above   : 290
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 34
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 1154
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 186
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.21/0.38  # Unit Clause-clause subsumption calls : 14
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 20
% 0.21/0.38  # BW rewrite match successes           : 4
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 6636
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.036 s
% 0.21/0.38  # System time              : 0.004 s
% 0.21/0.38  # Total time               : 0.040 s
% 0.21/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
