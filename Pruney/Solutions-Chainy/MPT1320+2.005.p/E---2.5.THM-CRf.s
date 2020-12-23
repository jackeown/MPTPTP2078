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

% Result     : Theorem 55.51s
% Output     : CNFRefutation 55.51s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 102 expanded)
%              Number of clauses        :   36 (  46 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  260 ( 431 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   70 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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

fof(c_0_10,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | m1_subset_1(k9_subset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_15,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k9_subset_1(X16,X17,X18) = k3_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_16,plain,(
    ! [X19,X20] : k1_setfam_1(k2_tarski(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X28,X29,X30,X31,X32,X34,X36] :
      ( ( m1_subset_1(esk2_5(X28,X29,X30,X31,X32),k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))
        | X31 != k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( r2_hidden(esk2_5(X28,X29,X30,X31,X32),X30)
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))
        | X31 != k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( k9_subset_1(u1_struct_0(X28),esk2_5(X28,X29,X30,X31,X32),X29) = X32
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))
        | X31 != k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r2_hidden(X34,X30)
        | k9_subset_1(u1_struct_0(X28),X34,X29) != X32
        | r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))
        | X31 != k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk3_4(X28,X29,X30,X31),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))
        | X31 = k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( ~ r2_hidden(esk3_4(X28,X29,X30,X31),X31)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ r2_hidden(X36,X30)
        | k9_subset_1(u1_struct_0(X28),X36,X29) != esk3_4(X28,X29,X30,X31)
        | X31 = k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk4_4(X28,X29,X30,X31),k1_zfmisc_1(u1_struct_0(X28)))
        | r2_hidden(esk3_4(X28,X29,X30,X31),X31)
        | X31 = k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( r2_hidden(esk4_4(X28,X29,X30,X31),X30)
        | r2_hidden(esk3_4(X28,X29,X30,X31),X31)
        | X31 = k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) )
      & ( k9_subset_1(u1_struct_0(X28),esk4_4(X28,X29,X30,X31),X29) = esk3_4(X28,X29,X30,X31)
        | r2_hidden(esk3_4(X28,X29,X30,X31),X31)
        | X31 = k1_tops_2(X28,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | m1_subset_1(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k9_subset_1(X2,X4,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X38,X39,X40] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))
      | m1_subset_1(k1_tops_2(X38,X39,X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X38,X39))))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X4,X5) != X1
    | X2 != k1_tops_2(X3,X5,X6)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5)))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X4,X6) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | u1_struct_0(k1_pre_topc(X26,X27)) = X27 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X4)
    | r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k9_subset_1(u1_struct_0(X2),X6,X3) != X1
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X6,X5) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X2)
    | r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k9_subset_1(u1_struct_0(X2),X6,X3) != X1
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r2_hidden(X6,X5) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

fof(c_0_43,negated_conjecture,(
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

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_tops_2(X2,X3,X4))
    | k1_tops_2(X2,X3,X4) != k1_tops_2(X2,X3,X5)
    | k1_setfam_1(k2_tarski(X6,X3)) != X1
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r2_hidden(X6,X5) ),
    inference(spm,[status(thm)],[c_0_41,c_0_24])).

cnf(c_0_45,plain,
    ( m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_42])).

fof(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    & r2_hidden(esk6_0,esk8_0)
    & ~ r2_hidden(k9_subset_1(u1_struct_0(esk5_0),esk6_0,esk7_0),k1_tops_2(esk5_0,esk7_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_47,plain,
    ( r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k1_tops_2(X3,X2,X4))
    | k1_tops_2(X3,X2,X4) != k1_tops_2(X3,X2,X5)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(X1,X5) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(esk5_0),esk6_0,esk7_0),k1_tops_2(esk5_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k1_setfam_1(k2_tarski(esk6_0,X1)),k1_tops_2(X2,X1,X3))
    | k1_tops_2(X2,X1,X3) != k1_tops_2(X2,X1,esk8_0)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),k1_tops_2(esk5_0,esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_24]),c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k1_setfam_1(k2_tarski(esk6_0,X1)),k1_tops_2(X2,X1,esk8_0))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 55.51/55.72  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 55.51/55.72  # and selection function SelectMaxLComplexAvoidPosPred.
% 55.51/55.72  #
% 55.51/55.72  # Preprocessing time       : 0.029 s
% 55.51/55.72  # Presaturation interreduction done
% 55.51/55.72  
% 55.51/55.72  # Proof found!
% 55.51/55.72  # SZS status Theorem
% 55.51/55.72  # SZS output start CNFRefutation
% 55.51/55.72  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 55.51/55.72  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 55.51/55.72  fof(dt_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 55.51/55.72  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 55.51/55.72  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 55.51/55.72  fof(d3_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))=>(X4=k1_tops_2(X1,X2,X3)<=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))=>(r2_hidden(X5,X4)<=>?[X6]:((m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X6,X3))&k9_subset_1(u1_struct_0(X1),X6,X2)=X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_2)).
% 55.51/55.72  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 55.51/55.72  fof(dt_k1_tops_2, axiom, ![X1, X2, X3]:(((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))&m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))))=>m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_2)).
% 55.51/55.72  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_pre_topc)).
% 55.51/55.72  fof(t41_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tops_2)).
% 55.51/55.72  fof(c_0_10, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 55.51/55.72  fof(c_0_11, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 55.51/55.72  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 55.51/55.72  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 55.51/55.72  fof(c_0_14, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(X13))|m1_subset_1(k9_subset_1(X13,X14,X15),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).
% 55.51/55.72  fof(c_0_15, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X16))|k9_subset_1(X16,X17,X18)=k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 55.51/55.72  fof(c_0_16, plain, ![X19, X20]:k1_setfam_1(k2_tarski(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 55.51/55.72  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 55.51/55.72  cnf(c_0_18, plain, (m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 55.51/55.72  cnf(c_0_19, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 55.51/55.72  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 55.51/55.72  fof(c_0_21, plain, ![X28, X29, X30, X31, X32, X34, X36]:(((((m1_subset_1(esk2_5(X28,X29,X30,X31,X32),k1_zfmisc_1(u1_struct_0(X28)))|~r2_hidden(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))|X31!=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(r2_hidden(esk2_5(X28,X29,X30,X31,X32),X30)|~r2_hidden(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))|X31!=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28)))&(k9_subset_1(u1_struct_0(X28),esk2_5(X28,X29,X30,X31,X32),X29)=X32|~r2_hidden(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))|X31!=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28)))&(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X28)))|~r2_hidden(X34,X30)|k9_subset_1(u1_struct_0(X28),X34,X29)!=X32|r2_hidden(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))|X31!=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28)))&((m1_subset_1(esk3_4(X28,X29,X30,X31),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29))))|X31=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&((~r2_hidden(esk3_4(X28,X29,X30,X31),X31)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X28)))|~r2_hidden(X36,X30)|k9_subset_1(u1_struct_0(X28),X36,X29)!=esk3_4(X28,X29,X30,X31))|X31=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(((m1_subset_1(esk4_4(X28,X29,X30,X31),k1_zfmisc_1(u1_struct_0(X28)))|r2_hidden(esk3_4(X28,X29,X30,X31),X31)|X31=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28))&(r2_hidden(esk4_4(X28,X29,X30,X31),X30)|r2_hidden(esk3_4(X28,X29,X30,X31),X31)|X31=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28)))&(k9_subset_1(u1_struct_0(X28),esk4_4(X28,X29,X30,X31),X29)=esk3_4(X28,X29,X30,X31)|r2_hidden(esk3_4(X28,X29,X30,X31),X31)|X31=k1_tops_2(X28,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X28,X29)))))|~m1_subset_1(X30,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X28))))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|~l1_pre_topc(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_2])])])])])).
% 55.51/55.72  fof(c_0_22, plain, ![X23, X24, X25]:(~r2_hidden(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(X25))|m1_subset_1(X23,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 55.51/55.72  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,k9_subset_1(X2,X4,X3))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 55.51/55.72  cnf(c_0_24, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 55.51/55.72  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 55.51/55.72  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 55.51/55.72  cnf(c_0_27, plain, (r2_hidden(X5,X6)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,X3)|k9_subset_1(u1_struct_0(X2),X1,X4)!=X5|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4))))|X6!=k1_tops_2(X2,X4,X3)|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X4)))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 55.51/55.72  cnf(c_0_28, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 55.51/55.72  fof(c_0_29, plain, ![X38, X39, X40]:(~l1_pre_topc(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|~m1_subset_1(X40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))|m1_subset_1(k1_tops_2(X38,X39,X40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X38,X39)))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_2])])).
% 55.51/55.72  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_setfam_1(k2_tarski(X4,X3)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 55.51/55.72  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 55.51/55.72  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 55.51/55.72  cnf(c_0_33, plain, (r2_hidden(X1,X2)|k9_subset_1(u1_struct_0(X3),X4,X5)!=X1|X2!=k1_tops_2(X3,X5,X6)|~l1_pre_topc(X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5)))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X3,X5))))|~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))|~r2_hidden(X4,X6)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 55.51/55.72  cnf(c_0_34, plain, (m1_subset_1(k1_tops_2(X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2)))))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 55.51/55.72  fof(c_0_35, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|u1_struct_0(k1_pre_topc(X26,X27))=X27)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 55.51/55.72  cnf(c_0_36, plain, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X4)|r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 55.51/55.72  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 55.51/55.72  cnf(c_0_38, plain, (r2_hidden(X1,k1_tops_2(X2,X3,X4))|k1_tops_2(X2,X3,X4)!=k1_tops_2(X2,X3,X5)|k9_subset_1(u1_struct_0(X2),X6,X3)!=X1|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X6,X5)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 55.51/55.72  cnf(c_0_39, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 55.51/55.72  cnf(c_0_40, plain, (r2_hidden(esk1_2(k1_setfam_1(k2_tarski(X1,X2)),X3),X2)|r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 55.51/55.72  cnf(c_0_41, plain, (r2_hidden(X1,k1_tops_2(X2,X3,X4))|k1_tops_2(X2,X3,X4)!=k1_tops_2(X2,X3,X5)|k9_subset_1(u1_struct_0(X2),X6,X3)!=X1|~l1_pre_topc(X2)|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r2_hidden(X6,X5)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 55.51/55.72  cnf(c_0_42, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_25, c_0_40])).
% 55.51/55.72  fof(c_0_43, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r2_hidden(X2,X4)=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),k1_tops_2(X1,X3,X4)))))))), inference(assume_negation,[status(cth)],[t41_tops_2])).
% 55.51/55.72  cnf(c_0_44, plain, (r2_hidden(X1,k1_tops_2(X2,X3,X4))|k1_tops_2(X2,X3,X4)!=k1_tops_2(X2,X3,X5)|k1_setfam_1(k2_tarski(X6,X3))!=X1|~l1_pre_topc(X2)|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r2_hidden(X6,X5)), inference(spm,[status(thm)],[c_0_41, c_0_24])).
% 55.51/55.72  cnf(c_0_45, plain, (m1_subset_1(k1_setfam_1(k2_tarski(X1,X2)),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_31, c_0_42])).
% 55.51/55.72  fof(c_0_46, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&(m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))&(r2_hidden(esk6_0,esk8_0)&~r2_hidden(k9_subset_1(u1_struct_0(esk5_0),esk6_0,esk7_0),k1_tops_2(esk5_0,esk7_0,esk8_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 55.51/55.72  cnf(c_0_47, plain, (r2_hidden(k1_setfam_1(k2_tarski(X1,X2)),k1_tops_2(X3,X2,X4))|k1_tops_2(X3,X2,X4)!=k1_tops_2(X3,X2,X5)|~l1_pre_topc(X3)|~m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~r2_hidden(X1,X5)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]), c_0_45])])).
% 55.51/55.72  cnf(c_0_48, negated_conjecture, (r2_hidden(esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 55.51/55.72  cnf(c_0_49, negated_conjecture, (~r2_hidden(k9_subset_1(u1_struct_0(esk5_0),esk6_0,esk7_0),k1_tops_2(esk5_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 55.51/55.72  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 55.51/55.72  cnf(c_0_51, negated_conjecture, (r2_hidden(k1_setfam_1(k2_tarski(esk6_0,X1)),k1_tops_2(X2,X1,X3))|k1_tops_2(X2,X1,X3)!=k1_tops_2(X2,X1,esk8_0)|~l1_pre_topc(X2)|~m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 55.51/55.72  cnf(c_0_52, negated_conjecture, (~r2_hidden(k1_setfam_1(k2_tarski(esk6_0,esk7_0)),k1_tops_2(esk5_0,esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_24]), c_0_50])])).
% 55.51/55.72  cnf(c_0_53, negated_conjecture, (r2_hidden(k1_setfam_1(k2_tarski(esk6_0,X1)),k1_tops_2(X2,X1,esk8_0))|~l1_pre_topc(X2)|~m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_51])).
% 55.51/55.72  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 55.51/55.72  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 55.51/55.72  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_50])]), ['proof']).
% 55.51/55.72  # SZS output end CNFRefutation
% 55.51/55.72  # Proof object total steps             : 57
% 55.51/55.72  # Proof object clause steps            : 36
% 55.51/55.72  # Proof object formula steps           : 21
% 55.51/55.72  # Proof object conjectures             : 12
% 55.51/55.72  # Proof object clause conjectures      : 9
% 55.51/55.72  # Proof object formula conjectures     : 3
% 55.51/55.72  # Proof object initial clauses used    : 17
% 55.51/55.72  # Proof object initial formulas used   : 10
% 55.51/55.72  # Proof object generating inferences   : 17
% 55.51/55.72  # Proof object simplifying inferences  : 10
% 55.51/55.72  # Training examples: 0 positive, 0 negative
% 55.51/55.72  # Parsed axioms                        : 10
% 55.51/55.72  # Removed by relevancy pruning/SinE    : 0
% 55.51/55.72  # Initial clauses                      : 26
% 55.51/55.72  # Removed in clause preprocessing      : 1
% 55.51/55.72  # Initial clauses in saturation        : 25
% 55.51/55.72  # Processed clauses                    : 22132
% 55.51/55.72  # ...of these trivial                  : 68
% 55.51/55.72  # ...subsumed                          : 9179
% 55.51/55.72  # ...remaining for further processing  : 12885
% 55.51/55.72  # Other redundant clauses eliminated   : 40
% 55.51/55.72  # Clauses deleted for lack of memory   : 3150
% 55.51/55.72  # Backward-subsumed                    : 153
% 55.51/55.72  # Backward-rewritten                   : 0
% 55.51/55.72  # Generated clauses                    : 1577226
% 55.51/55.72  # ...of the previous two non-trivial   : 1576634
% 55.51/55.72  # Contextual simplify-reflections      : 50
% 55.51/55.72  # Paramodulations                      : 1577044
% 55.51/55.72  # Factorizations                       : 0
% 55.51/55.72  # Equation resolutions                 : 182
% 55.51/55.72  # Propositional unsat checks           : 0
% 55.51/55.72  #    Propositional check models        : 0
% 55.51/55.72  #    Propositional check unsatisfiable : 0
% 55.51/55.72  #    Propositional clauses             : 0
% 55.51/55.72  #    Propositional clauses after purity: 0
% 55.51/55.72  #    Propositional unsat core size     : 0
% 55.51/55.72  #    Propositional preprocessing time  : 0.000
% 55.51/55.72  #    Propositional encoding time       : 0.000
% 55.51/55.72  #    Propositional solver time         : 0.000
% 55.51/55.72  #    Success case prop preproc time    : 0.000
% 55.51/55.72  #    Success case prop encoding time   : 0.000
% 55.51/55.72  #    Success case prop solver time     : 0.000
% 55.51/55.72  # Current number of processed clauses  : 12707
% 55.51/55.72  #    Positive orientable unit clauses  : 50
% 55.51/55.72  #    Positive unorientable unit clauses: 0
% 55.51/55.72  #    Negative unit clauses             : 2
% 55.51/55.72  #    Non-unit-clauses                  : 12655
% 55.51/55.72  # Current number of unprocessed clauses: 850700
% 55.51/55.72  # ...number of literals in the above   : 8315454
% 55.51/55.72  # Current number of archived formulas  : 0
% 55.51/55.72  # Current number of archived clauses   : 179
% 55.51/55.72  # Clause-clause subsumption calls (NU) : 82909477
% 55.51/55.72  # Rec. Clause-clause subsumption calls : 2365153
% 55.51/55.72  # Non-unit clause-clause subsumptions  : 9382
% 55.51/55.72  # Unit Clause-clause subsumption calls : 9933
% 55.51/55.72  # Rewrite failures with RHS unbound    : 0
% 55.51/55.72  # BW rewrite match attempts            : 1464
% 55.51/55.72  # BW rewrite match successes           : 0
% 55.51/55.72  # Condensation attempts                : 0
% 55.51/55.72  # Condensation successes               : 0
% 55.51/55.72  # Termbank termtop insertions          : 108783713
% 55.59/55.81  
% 55.59/55.81  # -------------------------------------------------
% 55.59/55.81  # User time                : 54.408 s
% 55.59/55.81  # System time              : 1.021 s
% 55.59/55.81  # Total time               : 55.429 s
% 55.59/55.81  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
