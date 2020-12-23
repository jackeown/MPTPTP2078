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
% DateTime   : Thu Dec  3 11:13:24 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of clauses        :   23 (  27 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  182 ( 314 expanded)
%              Number of equality atoms :   31 (  34 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   70 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t41_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( r2_hidden(X2,X4)
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
                 => ( X4 = k1_tops_2(X1,X2,X3)
                  <=> ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
                       => ( r2_hidden(X5,X4)
                        <=> ? [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
                              & r2_hidden(X6,X3)
                              & k9_subset_1(u1_struct_0(X1),X6,X2) = X5 ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k1_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(c_0_10,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_11,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( r2_hidden(X2,X4)
                     => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t41_tops_2])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26,X27,X29,X31] :
      ( ( m1_subset_1(esk1_5(X23,X24,X25,X26,X27),k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))
        | X26 != k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk1_5(X23,X24,X25,X26,X27),X25)
        | ~ r2_hidden(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))
        | X26 != k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( k9_subset_1(u1_struct_0(X23),esk1_5(X23,X24,X25,X26,X27),X24) = X27
        | ~ r2_hidden(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))
        | X26 != k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X29,X25)
        | k9_subset_1(u1_struct_0(X23),X29,X24) != X27
        | r2_hidden(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))
        | X26 != k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk2_4(X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))
        | X26 = k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( ~ r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ r2_hidden(X31,X25)
        | k9_subset_1(u1_struct_0(X23),X31,X24) != esk2_4(X23,X24,X25,X26)
        | X26 = k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( m1_subset_1(esk3_4(X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(X23)))
        | r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( r2_hidden(esk3_4(X23,X24,X25,X26),X25)
        | r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) )
      & ( k9_subset_1(u1_struct_0(X23),esk3_4(X23,X24,X25,X26),X24) = esk2_4(X23,X24,X25,X26)
        | r2_hidden(esk2_4(X23,X24,X25,X26),X26)
        | X26 = k1_tops_2(X23,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).

fof(c_0_17,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X33,X34,X35] :
      ( ~ l1_pre_topc(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))
      | m1_subset_1(k1_tops_2(X33,X34,X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X33,X34))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

fof(c_0_19,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | u1_struct_0(k1_pre_topc(X21,X22)) = X22 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & r2_hidden(esk5_0,esk7_0)
    & ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_23,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_24,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X11))
      | k9_subset_1(X11,X12,X13) = k3_xboole_0(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_25,plain,
    ( r2_hidden(X5,X6)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,X3)
    | k9_subset_1(u1_struct_0(X2),X1,X4) != X5
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4))))
    | X6 != k1_tops_2(X2,X4,X3)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4)))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_25,c_0_26])])]),c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk4_0,esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_33,c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30]),c_0_36]),c_0_37]),c_0_38]),c_0_29])])).

cnf(c_0_42,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.13/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.13/0.38  fof(t41_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_2)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(d3_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))=>(X4=k1_tops_2(X1,X2,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))=>(r2_hidden(X5,X4)<=>?[X6]:((m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X6,X3))&k9_subset_1(u1_struct_0(X1),X6,X2)=X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_2)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(dt_k1_tops_2, axiom, ![X1, X2, X3]:(((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))=>m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 0.13/0.38  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.13/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.13/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.13/0.38  fof(c_0_10, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X14, X15]:k1_setfam_1(k2_tarski(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t41_tops_2])).
% 0.13/0.38  fof(c_0_13, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_14, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_15, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_16, plain, ![X23, X24, X25, X26, X27, X29, X31]:(((((m1_subset_1(esk1_5(X23,X24,X25,X26,X27),k1_zfmisc_1(u1_struct_0(X23)))|~r2_hidden(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))|X26!=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(r2_hidden(esk1_5(X23,X24,X25,X26,X27),X25)|~r2_hidden(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))|X26!=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&(k9_subset_1(u1_struct_0(X23),esk1_5(X23,X24,X25,X26,X27),X24)=X27|~r2_hidden(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))|X26!=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X23)))|~r2_hidden(X29,X25)|k9_subset_1(u1_struct_0(X23),X29,X24)!=X27|r2_hidden(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))|X26!=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&((m1_subset_1(esk2_4(X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24))))|X26=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&((~r2_hidden(esk2_4(X23,X24,X25,X26),X26)|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X23)))|~r2_hidden(X31,X25)|k9_subset_1(u1_struct_0(X23),X31,X24)!=esk2_4(X23,X24,X25,X26))|X26=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(((m1_subset_1(esk3_4(X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(X23)))|r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23))&(r2_hidden(esk3_4(X23,X24,X25,X26),X25)|r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))&(k9_subset_1(u1_struct_0(X23),esk3_4(X23,X24,X25,X26),X24)=esk2_4(X23,X24,X25,X26)|r2_hidden(esk2_4(X23,X24,X25,X26),X26)|X26=k1_tops_2(X23,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X23,X24)))))|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X23))))|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|~l1_pre_topc(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  fof(c_0_18, plain, ![X33, X34, X35]:(~l1_pre_topc(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X33))))|m1_subset_1(k1_tops_2(X33,X34,X35),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X33,X34)))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).
% 0.13/0.38  fof(c_0_19, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|u1_struct_0(k1_pre_topc(X21,X22))=X22)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(r2_hidden(esk5_0,esk7_0)&~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.38  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  fof(c_0_23, plain, ![X9, X10]:k2_tarski(X9,X10)=k2_tarski(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.13/0.38  fof(c_0_24, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X11))|k9_subset_1(X11,X12,X13)=k3_xboole_0(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(X5,X6)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,X3)|k9_subset_1(u1_struct_0(X2),X1,X4)!=X5|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4))))|X6!=k1_tops_2(X2,X4,X3)|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4)))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_26, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, plain, (m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_28, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_31, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_32, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_33, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_35, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))|~l1_pre_topc(X1)|~r2_hidden(X2,X4)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_25, c_0_26])])]), c_0_27])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (u1_struct_0(k1_pre_topc(esk4_0,esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_39, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_40, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_33, c_0_15])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_30]), c_0_36]), c_0_37]), c_0_38]), c_0_29])])).
% 0.13/0.38  cnf(c_0_42, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 44
% 0.13/0.38  # Proof object clause steps            : 23
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 11
% 0.13/0.38  # Proof object clause conjectures      : 8
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 6
% 0.13/0.38  # Proof object simplifying inferences  : 16
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 24
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 23
% 0.13/0.38  # Processed clauses                    : 81
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 7
% 0.13/0.38  # ...remaining for further processing  : 71
% 0.13/0.38  # Other redundant clauses eliminated   : 5
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 130
% 0.13/0.38  # ...of the previous two non-trivial   : 120
% 0.13/0.38  # Contextual simplify-reflections      : 9
% 0.13/0.38  # Paramodulations                      : 126
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 5
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 44
% 0.13/0.38  #    Positive orientable unit clauses  : 11
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 30
% 0.13/0.38  # Current number of unprocessed clauses: 78
% 0.13/0.38  # ...number of literals in the above   : 438
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 24
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 640
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 166
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 16
% 0.13/0.38  # Unit Clause-clause subsumption calls : 8
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6416
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.039 s
% 0.13/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
