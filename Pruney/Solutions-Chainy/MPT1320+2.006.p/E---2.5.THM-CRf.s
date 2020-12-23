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
% DateTime   : Thu Dec  3 11:13:24 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   43 (  74 expanded)
%              Number of clauses        :   22 (  28 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  181 ( 321 expanded)
%              Number of equality atoms :   31 (  38 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   70 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

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

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X14) = k3_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_12,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_13,plain,(
    ! [X22,X23,X24,X25,X26,X28,X30] :
      ( ( m1_subset_1(esk1_5(X22,X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))
        | X25 != k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk1_5(X22,X23,X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))
        | X25 != k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( k9_subset_1(u1_struct_0(X22),esk1_5(X22,X23,X24,X25,X26),X23) = X26
        | ~ r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))
        | X25 != k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X28,X24)
        | k9_subset_1(u1_struct_0(X22),X28,X23) != X26
        | r2_hidden(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))
        | X25 != k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk2_4(X22,X23,X24,X25),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))
        | X25 = k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( ~ r2_hidden(esk2_4(X22,X23,X24,X25),X25)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ r2_hidden(X30,X24)
        | k9_subset_1(u1_struct_0(X22),X30,X23) != esk2_4(X22,X23,X24,X25)
        | X25 = k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk3_4(X22,X23,X24,X25),k1_zfmisc_1(u1_struct_0(X22)))
        | r2_hidden(esk2_4(X22,X23,X24,X25),X25)
        | X25 = k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( r2_hidden(esk3_4(X22,X23,X24,X25),X24)
        | r2_hidden(esk2_4(X22,X23,X24,X25),X25)
        | X25 = k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( k9_subset_1(u1_struct_0(X22),esk3_4(X22,X23,X24,X25),X23) = esk2_4(X22,X23,X24,X25)
        | r2_hidden(esk2_4(X22,X23,X24,X25),X25)
        | X25 = k1_tops_2(X22,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).

fof(c_0_14,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
      | m1_subset_1(k1_tops_2(X32,X33,X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X32,X33))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | u1_struct_0(k1_pre_topc(X20,X21)) = X21 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & r2_hidden(esk5_0,esk7_0)
    & ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_18,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_19,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_29,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_30,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_21,c_0_22])])]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk4_0,esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_26]),c_0_33]),c_0_34]),c_0_35]),c_0_25])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t41_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_2)).
% 0.14/0.38  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.14/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.14/0.38  fof(d3_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))=>(X4=k1_tops_2(X1,X2,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))=>(r2_hidden(X5,X4)<=>?[X6]:((m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X6,X3))&k9_subset_1(u1_struct_0(X1),X6,X2)=X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_2)).
% 0.14/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.38  fof(dt_k1_tops_2, axiom, ![X1, X2, X3]:(((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))=>m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 0.14/0.38  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 0.14/0.38  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 0.14/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.14/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.14/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t41_tops_2])).
% 0.14/0.38  fof(c_0_11, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X14)=k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.14/0.38  fof(c_0_12, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.14/0.38  fof(c_0_13, plain, ![X22, X23, X24, X25, X26, X28, X30]:(((((m1_subset_1(esk1_5(X22,X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(r2_hidden(esk1_5(X22,X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&(k9_subset_1(u1_struct_0(X22),esk1_5(X22,X23,X24,X25,X26),X23)=X26|~r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X28,X24)|k9_subset_1(u1_struct_0(X22),X28,X23)!=X26|r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&((m1_subset_1(esk2_4(X22,X23,X24,X25),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&((~r2_hidden(esk2_4(X22,X23,X24,X25),X25)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X30,X24)|k9_subset_1(u1_struct_0(X22),X30,X23)!=esk2_4(X22,X23,X24,X25))|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(((m1_subset_1(esk3_4(X22,X23,X24,X25),k1_zfmisc_1(u1_struct_0(X22)))|r2_hidden(esk2_4(X22,X23,X24,X25),X25)|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(r2_hidden(esk3_4(X22,X23,X24,X25),X24)|r2_hidden(esk2_4(X22,X23,X24,X25),X25)|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&(k9_subset_1(u1_struct_0(X22),esk3_4(X22,X23,X24,X25),X23)=esk2_4(X22,X23,X24,X25)|r2_hidden(esk2_4(X22,X23,X24,X25),X25)|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).
% 0.14/0.39  fof(c_0_14, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.39  fof(c_0_15, plain, ![X32, X33, X34]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|m1_subset_1(k1_tops_2(X32,X33,X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X32,X33)))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).
% 0.14/0.39  fof(c_0_16, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|u1_struct_0(k1_pre_topc(X20,X21))=X21)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 0.14/0.39  fof(c_0_17, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(r2_hidden(esk5_0,esk7_0)&~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.14/0.39  fof(c_0_18, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 0.14/0.39  cnf(c_0_19, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_21, plain, (r2_hidden(X5,X6)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,X3)|k9_subset_1(u1_struct_0(X2),X1,X4)!=X5|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4))))|X6!=k1_tops_2(X2,X4,X3)|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4)))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_22, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_23, plain, (m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  cnf(c_0_24, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_27, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_28, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.39  fof(c_0_29, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.14/0.39  fof(c_0_30, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_32, plain, (r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))|~l1_pre_topc(X1)|~r2_hidden(X2,X4)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X3))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_21, c_0_22])])]), c_0_23])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (u1_struct_0(k1_pre_topc(esk4_0,esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_36, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.39  cnf(c_0_37, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.39  cnf(c_0_38, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_26]), c_0_33]), c_0_34]), c_0_35]), c_0_25])])).
% 0.14/0.39  cnf(c_0_40, plain, (m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.14/0.39  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_25])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 43
% 0.14/0.39  # Proof object clause steps            : 22
% 0.14/0.39  # Proof object formula steps           : 21
% 0.14/0.39  # Proof object conjectures             : 11
% 0.14/0.39  # Proof object clause conjectures      : 8
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 14
% 0.14/0.39  # Proof object initial formulas used   : 10
% 0.14/0.39  # Proof object generating inferences   : 5
% 0.14/0.39  # Proof object simplifying inferences  : 17
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 10
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 23
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 21
% 0.14/0.39  # Processed clauses                    : 85
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 5
% 0.14/0.39  # ...remaining for further processing  : 80
% 0.14/0.39  # Other redundant clauses eliminated   : 5
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 0
% 0.14/0.39  # Generated clauses                    : 210
% 0.14/0.39  # ...of the previous two non-trivial   : 207
% 0.14/0.39  # Contextual simplify-reflections      : 10
% 0.14/0.39  # Paramodulations                      : 206
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 5
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 55
% 0.14/0.39  #    Positive orientable unit clauses  : 9
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 2
% 0.14/0.39  #    Non-unit-clauses                  : 44
% 0.14/0.39  # Current number of unprocessed clauses: 164
% 0.14/0.39  # ...number of literals in the above   : 994
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 23
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 886
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 328
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 15
% 0.14/0.39  # Unit Clause-clause subsumption calls : 6
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 5
% 0.14/0.39  # BW rewrite match successes           : 0
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 9901
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.037 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.042 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
