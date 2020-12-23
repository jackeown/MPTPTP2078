%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:24 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   45 (  67 expanded)
%              Number of clauses        :   26 (  29 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  246 ( 349 expanded)
%              Number of equality atoms :   43 (  49 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   70 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k1_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
     => m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_2)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_2)).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | m1_subset_1(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X32,X33,X34] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))
      | m1_subset_1(k1_tops_2(X32,X33,X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X32,X33))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X4,X5) != X1
    | X2 != k1_tops_2(X3,X5,X6)
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(X4,X6)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | u1_struct_0(k1_pre_topc(X20,X21)) = X21 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k9_subset_1(u1_struct_0(X2),X6,X3) != X1
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X6,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X14) = k3_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_20,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k9_subset_1(u1_struct_0(X2),X6,X3) != X1
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X6,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k3_xboole_0(X6,X3) != X1
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X6,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_31,negated_conjecture,(
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

cnf(c_0_32,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X4,X5))
    | k1_tops_2(X3,X4,X5) != k1_tops_2(X3,X4,X6)
    | k3_xboole_0(X7,X4) != k3_xboole_0(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(X7,X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & r2_hidden(esk5_0,esk7_0)
    & ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_35,plain,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X2,X4))
    | k1_tops_2(X3,X2,X4) != k1_tops_2(X3,X2,X5)
    | k3_xboole_0(X6,X2) != k3_xboole_0(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ r2_hidden(X6,X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X2,X4))
    | k1_tops_2(X3,X2,X4) != k1_tops_2(X3,X2,esk7_0)
    | k3_xboole_0(esk5_0,X2) != k3_xboole_0(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k3_xboole_0(esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_23]),c_0_38])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X2,esk7_0))
    | k3_xboole_0(esk5_0,X2) != k3_xboole_0(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.38/1.54  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 1.38/1.54  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.38/1.54  #
% 1.38/1.54  # Preprocessing time       : 0.028 s
% 1.38/1.54  # Presaturation interreduction done
% 1.38/1.54  
% 1.38/1.54  # Proof found!
% 1.38/1.54  # SZS status Theorem
% 1.38/1.54  # SZS output start CNFRefutation
% 1.38/1.54  fof(d3_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))=>(X4=k1_tops_2(X1,X2,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))=>(r2_hidden(X5,X4)<=>?[X6]:((m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X6,X3))&k9_subset_1(u1_struct_0(X1),X6,X2)=X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_2)).
% 1.38/1.54  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 1.38/1.54  fof(dt_k1_tops_2, axiom, ![X1, X2, X3]:(((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))=>m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 1.38/1.54  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 1.38/1.54  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 1.38/1.54  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 1.38/1.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.38/1.54  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.38/1.54  fof(t41_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_tops_2)).
% 1.38/1.54  fof(c_0_9, plain, ![X22, X23, X24, X25, X26, X28, X30]:(((((m1_subset_1(esk1_5(X22,X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(r2_hidden(esk1_5(X22,X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&(k9_subset_1(u1_struct_0(X22),esk1_5(X22,X23,X24,X25,X26),X23)=X26|~r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X28,X24)|k9_subset_1(u1_struct_0(X22),X28,X23)!=X26|r2_hidden(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25!=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&((m1_subset_1(esk2_4(X22,X23,X24,X25),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23))))|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&((~r2_hidden(esk2_4(X22,X23,X24,X25),X25)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X22)))|~r2_hidden(X30,X24)|k9_subset_1(u1_struct_0(X22),X30,X23)!=esk2_4(X22,X23,X24,X25))|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(((m1_subset_1(esk3_4(X22,X23,X24,X25),k1_zfmisc_1(u1_struct_0(X22)))|r2_hidden(esk2_4(X22,X23,X24,X25),X25)|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(r2_hidden(esk3_4(X22,X23,X24,X25),X24)|r2_hidden(esk2_4(X22,X23,X24,X25),X25)|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))&(k9_subset_1(u1_struct_0(X22),esk3_4(X22,X23,X24,X25),X23)=esk2_4(X22,X23,X24,X25)|r2_hidden(esk2_4(X22,X23,X24,X25),X25)|X25=k1_tops_2(X22,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X22,X23)))))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X22))))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).
% 1.38/1.54  fof(c_0_10, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|m1_subset_1(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 1.38/1.54  cnf(c_0_11, plain, (r2_hidden(X5,X6)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,X3)|k9_subset_1(u1_struct_0(X2),X1,X4)!=X5|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4))))|X6!=k1_tops_2(X2,X4,X3)|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4)))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.38/1.54  cnf(c_0_12, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.38/1.54  fof(c_0_13, plain, ![X32, X33, X34]:(~l1_pre_topc(X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X32))))|m1_subset_1(k1_tops_2(X32,X33,X34),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X32,X33)))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).
% 1.38/1.54  cnf(c_0_14, plain, (r2_hidden(X1,X2)|k9_subset_1(u1_struct_0(X3),X4,X5)!=X1|X2!=k1_tops_2(X3,X5,X6)|~l1_pre_topc(X3)|~r2_hidden(X4,X6)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5)))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5))))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))), inference(csr,[status(thm)],[c_0_11, c_0_12])).
% 1.38/1.54  cnf(c_0_15, plain, (m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.38/1.54  fof(c_0_16, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|u1_struct_0(k1_pre_topc(X20,X21))=X21)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 1.38/1.54  cnf(c_0_17, plain, (r2_hidden(X1,k1_tops_2(X2,X3,X4))|k1_tops_2(X2,X3,X4)!=k1_tops_2(X2,X3,X5)|k9_subset_1(u1_struct_0(X2),X6,X3)!=X1|~l1_pre_topc(X2)|~r2_hidden(X6,X5)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.38/1.54  cnf(c_0_18, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.38/1.54  fof(c_0_19, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X14)=k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 1.38/1.54  fof(c_0_20, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X9))|m1_subset_1(k9_subset_1(X9,X10,X11),k1_zfmisc_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 1.38/1.54  fof(c_0_21, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.38/1.54  cnf(c_0_22, plain, (r2_hidden(X1,k1_tops_2(X2,X3,X4))|k1_tops_2(X2,X3,X4)!=k1_tops_2(X2,X3,X5)|k9_subset_1(u1_struct_0(X2),X6,X3)!=X1|~l1_pre_topc(X2)|~r2_hidden(X6,X5)|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 1.38/1.54  cnf(c_0_23, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.38/1.54  cnf(c_0_24, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.38/1.54  fof(c_0_25, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.38/1.54  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.38/1.54  cnf(c_0_27, plain, (r2_hidden(X1,k1_tops_2(X2,X3,X4))|k1_tops_2(X2,X3,X4)!=k1_tops_2(X2,X3,X5)|k3_xboole_0(X6,X3)!=X1|~l1_pre_topc(X2)|~r2_hidden(X6,X5)|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.38/1.54  cnf(c_0_28, plain, (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 1.38/1.54  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.38/1.54  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 1.38/1.54  fof(c_0_31, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t41_tops_2])).
% 1.38/1.54  cnf(c_0_32, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X4,X5))|k1_tops_2(X3,X4,X5)!=k1_tops_2(X3,X4,X6)|k3_xboole_0(X7,X4)!=k3_xboole_0(X1,X2)|~l1_pre_topc(X3)|~r2_hidden(X7,X6)|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.38/1.54  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.38/1.54  fof(c_0_34, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(r2_hidden(esk5_0,esk7_0)&~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 1.38/1.54  cnf(c_0_35, plain, (r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X2,X4))|k1_tops_2(X3,X2,X4)!=k1_tops_2(X3,X2,X5)|k3_xboole_0(X6,X2)!=k3_xboole_0(X1,X2)|~l1_pre_topc(X3)|~r2_hidden(X6,X5)|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.38/1.54  cnf(c_0_36, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.38/1.54  cnf(c_0_37, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.38/1.54  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.38/1.54  cnf(c_0_39, negated_conjecture, (r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X2,X4))|k1_tops_2(X3,X2,X4)!=k1_tops_2(X3,X2,esk7_0)|k3_xboole_0(esk5_0,X2)!=k3_xboole_0(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.38/1.54  cnf(c_0_40, negated_conjecture, (~r2_hidden(k3_xboole_0(esk5_0,esk6_0),k1_tops_2(esk4_0,esk6_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_23]), c_0_38])])).
% 1.38/1.54  cnf(c_0_41, negated_conjecture, (r2_hidden(k3_xboole_0(X1,X2),k1_tops_2(X3,X2,esk7_0))|k3_xboole_0(esk5_0,X2)!=k3_xboole_0(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_39])).
% 1.38/1.54  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.38/1.54  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.38/1.54  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_38])]), ['proof']).
% 1.38/1.54  # SZS output end CNFRefutation
% 1.38/1.54  # Proof object total steps             : 45
% 1.38/1.54  # Proof object clause steps            : 26
% 1.38/1.54  # Proof object formula steps           : 19
% 1.38/1.54  # Proof object conjectures             : 12
% 1.38/1.54  # Proof object clause conjectures      : 9
% 1.38/1.54  # Proof object formula conjectures     : 3
% 1.38/1.54  # Proof object initial clauses used    : 13
% 1.38/1.54  # Proof object initial formulas used   : 9
% 1.38/1.54  # Proof object generating inferences   : 11
% 1.38/1.54  # Proof object simplifying inferences  : 8
% 1.38/1.54  # Training examples: 0 positive, 0 negative
% 1.38/1.54  # Parsed axioms                        : 9
% 1.38/1.54  # Removed by relevancy pruning/SinE    : 0
% 1.38/1.54  # Initial clauses                      : 25
% 1.38/1.54  # Removed in clause preprocessing      : 0
% 1.38/1.54  # Initial clauses in saturation        : 25
% 1.38/1.54  # Processed clauses                    : 2257
% 1.38/1.54  # ...of these trivial                  : 31
% 1.38/1.54  # ...subsumed                          : 619
% 1.38/1.54  # ...remaining for further processing  : 1607
% 1.38/1.54  # Other redundant clauses eliminated   : 44
% 1.38/1.54  # Clauses deleted for lack of memory   : 0
% 1.38/1.54  # Backward-subsumed                    : 22
% 1.38/1.54  # Backward-rewritten                   : 0
% 1.38/1.54  # Generated clauses                    : 15599
% 1.38/1.54  # ...of the previous two non-trivial   : 15467
% 1.38/1.54  # Contextual simplify-reflections      : 9
% 1.38/1.54  # Paramodulations                      : 15489
% 1.38/1.54  # Factorizations                       : 0
% 1.38/1.54  # Equation resolutions                 : 110
% 1.38/1.54  # Propositional unsat checks           : 0
% 1.38/1.54  #    Propositional check models        : 0
% 1.38/1.54  #    Propositional check unsatisfiable : 0
% 1.38/1.54  #    Propositional clauses             : 0
% 1.38/1.54  #    Propositional clauses after purity: 0
% 1.38/1.54  #    Propositional unsat core size     : 0
% 1.38/1.54  #    Propositional preprocessing time  : 0.000
% 1.38/1.54  #    Propositional encoding time       : 0.000
% 1.38/1.54  #    Propositional solver time         : 0.000
% 1.38/1.54  #    Success case prop preproc time    : 0.000
% 1.38/1.54  #    Success case prop encoding time   : 0.000
% 1.38/1.54  #    Success case prop solver time     : 0.000
% 1.38/1.54  # Current number of processed clauses  : 1559
% 1.38/1.54  #    Positive orientable unit clauses  : 7
% 1.38/1.54  #    Positive unorientable unit clauses: 0
% 1.38/1.54  #    Negative unit clauses             : 3
% 1.38/1.54  #    Non-unit-clauses                  : 1549
% 1.38/1.54  # Current number of unprocessed clauses: 13177
% 1.38/1.54  # ...number of literals in the above   : 183873
% 1.38/1.54  # Current number of archived formulas  : 0
% 1.38/1.54  # Current number of archived clauses   : 46
% 1.38/1.54  # Clause-clause subsumption calls (NU) : 1277600
% 1.38/1.54  # Rec. Clause-clause subsumption calls : 49047
% 1.38/1.54  # Non-unit clause-clause subsumptions  : 649
% 1.38/1.54  # Unit Clause-clause subsumption calls : 32
% 1.38/1.54  # Rewrite failures with RHS unbound    : 0
% 1.38/1.54  # BW rewrite match attempts            : 4
% 1.38/1.54  # BW rewrite match successes           : 0
% 1.38/1.54  # Condensation attempts                : 0
% 1.38/1.54  # Condensation successes               : 0
% 1.38/1.54  # Termbank termtop insertions          : 1022948
% 1.38/1.54  
% 1.38/1.54  # -------------------------------------------------
% 1.38/1.54  # User time                : 1.178 s
% 1.38/1.54  # System time              : 0.020 s
% 1.38/1.54  # Total time               : 1.198 s
% 1.38/1.54  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
