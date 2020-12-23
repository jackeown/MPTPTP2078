%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:12 EST 2020

% Result     : Theorem 49.22s
% Output     : CNFRefutation 49.22s
% Verified   : 
% Statistics : Number of formulae       :  169 (3610 expanded)
%              Number of clauses        :  122 (1583 expanded)
%              Number of leaves         :   23 ( 963 expanded)
%              Depth                    :   22
%              Number of atoms          :  527 (10060 expanded)
%              Number of equality atoms :   58 (1075 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_xboole_0(X2,X4) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(t44_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,k3_subset_1(X1,X3))
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t88_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> r1_tarski(X2,k2_tops_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t73_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t67_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & r1_xboole_0(X2,X3) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(commutativity_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k4_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(t65_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(t62_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(dt_k2_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(c_0_23,plain,(
    ! [X8,X9,X10,X11] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X10,X11)
      | ~ r1_xboole_0(X9,X11)
      | r1_xboole_0(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).

fof(c_0_24,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r1_xboole_0(X32,k3_subset_1(X31,X33))
        | r1_tarski(X32,X33)
        | ~ m1_subset_1(X33,k1_zfmisc_1(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) )
      & ( ~ r1_tarski(X32,X33)
        | r1_xboole_0(X32,k3_subset_1(X31,X33))
        | ~ m1_subset_1(X33,k1_zfmisc_1(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).

fof(c_0_25,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X28))
      | ~ m1_subset_1(X30,k1_zfmisc_1(X28))
      | ~ r1_tarski(X29,k3_subset_1(X28,X30))
      | r1_tarski(X30,k3_subset_1(X28,X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

fof(c_0_26,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_27,plain,(
    ! [X34] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X34)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4)
    | ~ r1_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_xboole_0(X1,k3_subset_1(X3,X2))
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r1_tarski(X2,k3_subset_1(X4,X3))
    | ~ r1_tarski(X1,X5)
    | ~ r1_tarski(X5,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tops_1(X2,X1)
            <=> r1_tarski(X2,k2_tops_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tops_1])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_32])])).

fof(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ v2_tops_1(esk2_0,esk1_0)
      | ~ r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)) )
    & ( v2_tops_1(esk2_0,esk1_0)
      | r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_41,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | k3_subset_1(X23,k3_subset_1(X23,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

fof(c_0_42,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | m1_subset_1(k3_subset_1(X21,X22),k1_zfmisc_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_40])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

fof(c_0_51,plain,(
    ! [X54,X55] :
      ( ~ l1_pre_topc(X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))
      | r1_xboole_0(k1_tops_1(X54,X55),k2_tops_1(X54,X55)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_tops_1])])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_53,plain,(
    ! [X40,X41] :
      ( ~ l1_pre_topc(X40)
      | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
      | k1_tops_1(X40,X41) = k3_subset_1(u1_struct_0(X40),k2_pre_topc(X40,k3_subset_1(u1_struct_0(X40),X41))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_54,plain,
    ( k3_subset_1(X1,k1_xboole_0) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

cnf(c_0_55,plain,
    ( r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_47]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_49])).

fof(c_0_57,plain,(
    ! [X48,X49] :
      ( ~ l1_pre_topc(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | r1_tarski(k1_tops_1(X48,X49),X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_31])])).

cnf(c_0_59,plain,
    ( r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X1,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_48])).

cnf(c_0_61,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_62,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | m1_subset_1(k2_pre_topc(X38,X39),k1_zfmisc_1(u1_struct_0(X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_63,plain,
    ( k3_subset_1(X1,k1_xboole_0) = k3_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_32])]),c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_40])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ r1_tarski(X3,k1_xboole_0)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_58])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X2,k2_tops_1(X3,X4))
    | ~ r1_tarski(X1,k1_tops_1(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_69,plain,(
    ! [X12,X13,X14] :
      ( ~ r1_tarski(X12,X13)
      | ~ r1_tarski(X12,X14)
      | ~ r1_xboole_0(X13,X14)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_47]),c_0_48])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_60])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_61])).

cnf(c_0_73,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_63])).

cnf(c_0_75,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(X1,esk2_0)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k1_tops_1(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_32])])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_40])).

fof(c_0_78,plain,(
    ! [X44,X45] :
      ( ( ~ v2_tops_1(X45,X44)
        | v1_tops_1(k3_subset_1(u1_struct_0(X44),X45),X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X44),X45),X44)
        | v2_tops_1(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

fof(c_0_79,plain,(
    ! [X56,X57] :
      ( ( ~ v2_tops_1(X57,X56)
        | k1_tops_1(X56,X57) = k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ l1_pre_topc(X56) )
      & ( k1_tops_1(X56,X57) != k1_xboole_0
        | v2_tops_1(X57,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,k2_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_44]),c_0_68])])).

cnf(c_0_82,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_83,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_84,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_40]),c_0_48])).

cnf(c_0_85,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_47]),c_0_73]),c_0_48])).

cnf(c_0_87,plain,
    ( k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_32]),c_0_31])])).

cnf(c_0_88,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_32]),c_0_31])])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(X1,k1_xboole_0),esk2_0)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_40])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,k1_tops_1(X2,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_65]),c_0_32])])).

fof(c_0_91,plain,(
    ! [X42,X43] :
      ( ( ~ v1_tops_1(X43,X42)
        | k2_pre_topc(X42,X43) = k2_struct_0(X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X42) )
      & ( k2_pre_topc(X42,X43) != k2_struct_0(X42)
        | v1_tops_1(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
        | ~ l1_pre_topc(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_92,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_93,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_94,plain,
    ( k1_tops_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_65]),c_0_32])])).

cnf(c_0_95,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_96,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_97,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_44])).

cnf(c_0_98,plain,
    ( m1_subset_1(k1_tops_1(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_99,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ r1_tarski(X1,k1_tops_1(X3,k1_xboole_0))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_89])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(X1,k1_xboole_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_40])).

cnf(c_0_101,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_102,plain,
    ( v1_tops_1(X1,X2)
    | ~ v2_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_47]),c_0_48])).

cnf(c_0_103,plain,
    ( v2_tops_1(k1_xboole_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_32])])).

cnf(c_0_104,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0)
    | r1_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_40])).

cnf(c_0_105,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_71])).

cnf(c_0_106,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_tops_1(esk1_0,k1_xboole_0))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k1_xboole_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_68])])).

cnf(c_0_107,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(X1,k1_xboole_0),X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_40])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k1_tops_1(X1,k1_xboole_0),esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k1_tops_1(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_100]),c_0_44])])).

cnf(c_0_109,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_48])).

cnf(c_0_110,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_111,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_101,c_0_48])).

cnf(c_0_112,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_87]),c_0_88])]),c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_tops_1(esk2_0,esk1_0)
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_104])).

cnf(c_0_114,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_61])).

cnf(c_0_115,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_xboole_0(esk2_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_44])).

cnf(c_0_116,negated_conjecture,
    ( r1_xboole_0(esk2_0,k1_tops_1(esk1_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_68]),c_0_40])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k1_xboole_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_68]),c_0_32])])).

cnf(c_0_118,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_35]),c_0_32])])).

cnf(c_0_119,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_47]),c_0_48])).

cnf(c_0_120,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),k1_xboole_0)) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_32])])).

cnf(c_0_121,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0
    | v2_tops_1(esk2_0,esk1_0)
    | ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_40])).

cnf(c_0_122,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_73]),c_0_48])).

cnf(c_0_123,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_tops_1(esk1_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])])).

cnf(c_0_124,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_48])).

cnf(c_0_125,plain,
    ( v2_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v1_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_119,c_0_61])).

cnf(c_0_126,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_92])).

cnf(c_0_127,plain,
    ( m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_120]),c_0_88])])).

cnf(c_0_128,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) = k1_xboole_0
    | v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_65]),c_0_68]),c_0_44])])).

cnf(c_0_129,plain,
    ( k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,k1_xboole_0)) = k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_120]),c_0_32])])).

cnf(c_0_130,negated_conjecture,
    ( k1_tops_1(esk1_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_109]),c_0_68]),c_0_32])])).

fof(c_0_131,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,k2_xboole_0(X16,X17))
      | ~ r1_xboole_0(X15,X17)
      | r1_tarski(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

fof(c_0_132,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
      | k4_subset_1(X25,X26,X27) = k2_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_133,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r1_tarski(X1,k3_subset_1(X4,X3))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_124])).

cnf(c_0_134,plain,
    ( v2_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v2_tops_1(X2,X1)
    | ~ v1_tops_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_127])).

cnf(c_0_135,negated_conjecture,
    ( v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_128]),c_0_68]),c_0_44])])).

cnf(c_0_136,negated_conjecture,
    ( k2_struct_0(esk1_0) = k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_68])])).

cnf(c_0_137,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_131])).

cnf(c_0_138,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_132])).

fof(c_0_139,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | k4_subset_1(X18,X19,X20) = k4_subset_1(X18,X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).

fof(c_0_140,plain,(
    ! [X52,X53] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | k2_pre_topc(X52,X53) = k4_subset_1(u1_struct_0(X52),X53,k2_tops_1(X52,X53)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).

fof(c_0_141,plain,(
    ! [X50,X51] :
      ( ~ l1_pre_topc(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | k2_tops_1(X50,X51) = k2_tops_1(X50,k3_subset_1(u1_struct_0(X50),X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).

cnf(c_0_142,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_35]),c_0_32])])).

cnf(c_0_143,plain,
    ( v1_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)
    | ~ v2_tops_1(k1_tops_1(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_102,c_0_61])).

cnf(c_0_144,negated_conjecture,
    ( v2_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_44]),c_0_135]),c_0_136]),c_0_68])])).

cnf(c_0_145,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_130]),c_0_68]),c_0_32])])).

cnf(c_0_146,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k4_subset_1(X4,X2,X3)) ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_147,plain,
    ( k4_subset_1(X2,X1,X3) = k4_subset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_139])).

cnf(c_0_148,plain,
    ( k2_pre_topc(X1,X2) = k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_149,plain,
    ( k2_tops_1(X1,X2) = k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

fof(c_0_150,plain,(
    ! [X46,X47] :
      ( ~ l1_pre_topc(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | m1_subset_1(k2_tops_1(X46,X47),k1_zfmisc_1(u1_struct_0(X46))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).

cnf(c_0_151,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_142,c_0_44])).

cnf(c_0_152,plain,
    ( v1_tops_1(k2_struct_0(X1),X1)
    | ~ v2_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_126]),c_0_127])).

cnf(c_0_153,negated_conjecture,
    ( v2_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_92]),c_0_145]),c_0_68]),c_0_32])])).

cnf(c_0_154,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k4_subset_1(X4,X3,X2)) ),
    inference(spm,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_155,plain,
    ( k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_48])).

cnf(c_0_156,plain,
    ( m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_150])).

cnf(c_0_157,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_151])).

cnf(c_0_158,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_44]),c_0_136]),c_0_153]),c_0_135]),c_0_68])])).

cnf(c_0_159,plain,
    ( r1_tarski(X1,k2_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X1,k3_subset_1(u1_struct_0(X2),X3))
    | ~ r1_tarski(X1,k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_156]),c_0_48])).

cnf(c_0_160,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk1_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_48])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_157,c_0_61])).

cnf(c_0_162,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0)) = k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_158]),c_0_136]),c_0_68]),c_0_32])])).

cnf(c_0_163,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0)
    | ~ r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_164,plain,
    ( r1_tarski(X1,k2_tops_1(X2,X3))
    | ~ v2_tops_1(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_xboole_0(X1,k3_subset_1(u1_struct_0(X2),X3))
    | ~ r1_tarski(X1,k2_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_126])).

cnf(c_0_165,negated_conjecture,
    ( r1_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_84]),c_0_44])])).

cnf(c_0_166,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_162]),c_0_68]),c_0_88]),c_0_44]),c_0_32]),c_0_130]),c_0_31])])).

cnf(c_0_167,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_163,c_0_135])])).

cnf(c_0_168,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_135]),c_0_68]),c_0_44]),c_0_136]),c_0_166])]),c_0_167]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 49.22/49.49  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 49.22/49.49  # and selection function SelectComplexExceptUniqMaxHorn.
% 49.22/49.49  #
% 49.22/49.49  # Preprocessing time       : 0.029 s
% 49.22/49.49  # Presaturation interreduction done
% 49.22/49.49  
% 49.22/49.49  # Proof found!
% 49.22/49.49  # SZS status Theorem
% 49.22/49.49  # SZS output start CNFRefutation
% 49.22/49.49  fof(t64_xboole_1, axiom, ![X1, X2, X3, X4]:(((r1_tarski(X1,X2)&r1_tarski(X3,X4))&r1_xboole_0(X2,X4))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_xboole_1)).
% 49.22/49.49  fof(t44_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_xboole_0(X2,k3_subset_1(X1,X3))<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 49.22/49.49  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 49.22/49.49  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 49.22/49.49  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 49.22/49.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 49.22/49.49  fof(t88_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>r1_tarski(X2,k2_tops_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 49.22/49.49  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 49.22/49.49  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 49.22/49.49  fof(t73_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tops_1)).
% 49.22/49.49  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 49.22/49.49  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 49.22/49.49  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 49.22/49.49  fof(t67_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&r1_xboole_0(X2,X3))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 49.22/49.49  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_1)).
% 49.22/49.49  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 49.22/49.49  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tops_1)).
% 49.22/49.49  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 49.22/49.49  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 49.22/49.49  fof(commutativity_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k4_subset_1(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 49.22/49.49  fof(t65_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 49.22/49.49  fof(t62_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_1)).
% 49.22/49.49  fof(dt_k2_tops_1, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 49.22/49.49  fof(c_0_23, plain, ![X8, X9, X10, X11]:(~r1_tarski(X8,X9)|~r1_tarski(X10,X11)|~r1_xboole_0(X9,X11)|r1_xboole_0(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_xboole_1])])).
% 49.22/49.49  fof(c_0_24, plain, ![X31, X32, X33]:((~r1_xboole_0(X32,k3_subset_1(X31,X33))|r1_tarski(X32,X33)|~m1_subset_1(X33,k1_zfmisc_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(X31)))&(~r1_tarski(X32,X33)|r1_xboole_0(X32,k3_subset_1(X31,X33))|~m1_subset_1(X33,k1_zfmisc_1(X31))|~m1_subset_1(X32,k1_zfmisc_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_subset_1])])])])).
% 49.22/49.49  fof(c_0_25, plain, ![X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(X28))|(~m1_subset_1(X30,k1_zfmisc_1(X28))|(~r1_tarski(X29,k3_subset_1(X28,X30))|r1_tarski(X30,k3_subset_1(X28,X29))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 49.22/49.49  fof(c_0_26, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 49.22/49.49  fof(c_0_27, plain, ![X34]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X34)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 49.22/49.49  cnf(c_0_28, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)|~r1_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 49.22/49.49  cnf(c_0_29, plain, (r1_xboole_0(X1,k3_subset_1(X3,X2))|~r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 49.22/49.49  cnf(c_0_30, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 49.22/49.49  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 49.22/49.49  cnf(c_0_32, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 49.22/49.49  fof(c_0_33, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 49.22/49.49  cnf(c_0_34, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X5,k1_zfmisc_1(X4))|~r1_tarski(X2,k3_subset_1(X4,X3))|~r1_tarski(X1,X5)|~r1_tarski(X5,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 49.22/49.49  cnf(c_0_35, plain, (r1_tarski(X1,k3_subset_1(X2,k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 49.22/49.49  fof(c_0_36, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>r1_tarski(X2,k2_tops_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t88_tops_1])).
% 49.22/49.49  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 49.22/49.49  cnf(c_0_38, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_32])])).
% 49.22/49.49  fof(c_0_39, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((~v2_tops_1(esk2_0,esk1_0)|~r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))&(v2_tops_1(esk2_0,esk1_0)|r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 49.22/49.49  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 49.22/49.49  fof(c_0_41, plain, ![X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X23))|k3_subset_1(X23,k3_subset_1(X23,X24))=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 49.22/49.49  fof(c_0_42, plain, ![X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|m1_subset_1(k3_subset_1(X21,X22),k1_zfmisc_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 49.22/49.49  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_32]), c_0_31])])).
% 49.22/49.49  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 49.22/49.49  cnf(c_0_45, plain, (r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X4,k1_zfmisc_1(X2))|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_34, c_0_40])).
% 49.22/49.49  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 49.22/49.49  cnf(c_0_47, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 49.22/49.49  cnf(c_0_48, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 49.22/49.49  cnf(c_0_49, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 49.22/49.49  cnf(c_0_50, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 49.22/49.49  fof(c_0_51, plain, ![X54, X55]:(~l1_pre_topc(X54)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X54)))|r1_xboole_0(k1_tops_1(X54,X55),k2_tops_1(X54,X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_tops_1])])])).
% 49.22/49.49  cnf(c_0_52, plain, (r1_tarski(X1,X3)|~r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 49.22/49.49  fof(c_0_53, plain, ![X40, X41]:(~l1_pre_topc(X40)|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|k1_tops_1(X40,X41)=k3_subset_1(u1_struct_0(X40),k2_pre_topc(X40,k3_subset_1(u1_struct_0(X40),X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 49.22/49.49  cnf(c_0_54, plain, (k3_subset_1(X1,k1_xboole_0)=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 49.22/49.49  cnf(c_0_55, plain, (r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_47]), c_0_48])).
% 49.22/49.49  cnf(c_0_56, negated_conjecture, (r1_xboole_0(X1,X2)|~r1_tarski(X2,esk2_0)|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_49])).
% 49.22/49.49  fof(c_0_57, plain, ![X48, X49]:(~l1_pre_topc(X48)|(~m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))|r1_tarski(k1_tops_1(X48,X49),X49))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 49.22/49.49  cnf(c_0_58, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_31])])).
% 49.22/49.49  cnf(c_0_59, plain, (r1_xboole_0(k1_tops_1(X1,X2),k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 49.22/49.49  cnf(c_0_60, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X1,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_48])).
% 49.22/49.49  cnf(c_0_61, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 49.22/49.49  fof(c_0_62, plain, ![X38, X39]:(~l1_pre_topc(X38)|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))|m1_subset_1(k2_pre_topc(X38,X39),k1_zfmisc_1(u1_struct_0(X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 49.22/49.49  cnf(c_0_63, plain, (k3_subset_1(X1,k1_xboole_0)=k3_subset_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_32])]), c_0_48])).
% 49.22/49.49  cnf(c_0_64, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_40])).
% 49.22/49.49  cnf(c_0_65, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 49.22/49.49  cnf(c_0_66, negated_conjecture, (r1_xboole_0(X1,X2)|~r1_tarski(X2,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~r1_tarski(X3,k1_xboole_0)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_58])).
% 49.22/49.49  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|~l1_pre_topc(X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~r1_tarski(X2,k2_tops_1(X3,X4))|~r1_tarski(X1,k1_tops_1(X3,X4))), inference(spm,[status(thm)],[c_0_28, c_0_59])).
% 49.22/49.49  cnf(c_0_68, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 49.22/49.49  fof(c_0_69, plain, ![X12, X13, X14]:(~r1_tarski(X12,X13)|~r1_tarski(X12,X14)|~r1_xboole_0(X13,X14)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_xboole_1])])).
% 49.22/49.49  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_47]), c_0_48])).
% 49.22/49.49  cnf(c_0_71, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_30, c_0_60])).
% 49.22/49.49  cnf(c_0_72, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_61])).
% 49.22/49.49  cnf(c_0_73, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 49.22/49.49  cnf(c_0_74, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_63])).
% 49.22/49.49  cnf(c_0_75, plain, (m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_63])).
% 49.22/49.49  cnf(c_0_76, negated_conjecture, (r1_xboole_0(X1,esk2_0)|~l1_pre_topc(X2)|~r1_tarski(X1,k1_tops_1(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_32])])).
% 49.22/49.49  cnf(c_0_77, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_40])).
% 49.22/49.49  fof(c_0_78, plain, ![X44, X45]:((~v2_tops_1(X45,X44)|v1_tops_1(k3_subset_1(u1_struct_0(X44),X45),X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))&(~v1_tops_1(k3_subset_1(u1_struct_0(X44),X45),X44)|v2_tops_1(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 49.22/49.49  fof(c_0_79, plain, ![X56, X57]:((~v2_tops_1(X57,X56)|k1_tops_1(X56,X57)=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|~l1_pre_topc(X56))&(k1_tops_1(X56,X57)!=k1_xboole_0|v2_tops_1(X57,X56)|~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|~l1_pre_topc(X56))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 49.22/49.49  cnf(c_0_80, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 49.22/49.49  cnf(c_0_81, negated_conjecture, (r1_xboole_0(X1,X2)|~r1_tarski(X2,k2_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_44]), c_0_68])])).
% 49.22/49.49  cnf(c_0_82, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 49.22/49.49  cnf(c_0_83, plain, (X1=k1_xboole_0|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 49.22/49.49  cnf(c_0_84, plain, (r1_xboole_0(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_40]), c_0_48])).
% 49.22/49.49  cnf(c_0_85, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 49.22/49.49  cnf(c_0_86, plain, (m1_subset_1(k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_47]), c_0_73]), c_0_48])).
% 49.22/49.49  cnf(c_0_87, plain, (k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_32]), c_0_31])])).
% 49.22/49.49  cnf(c_0_88, plain, (m1_subset_1(k3_subset_1(X1,k1_xboole_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_32]), c_0_31])])).
% 49.22/49.49  cnf(c_0_89, negated_conjecture, (r1_xboole_0(k1_tops_1(X1,k1_xboole_0),esk2_0)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_76, c_0_40])).
% 49.22/49.49  cnf(c_0_90, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~l1_pre_topc(X2)|~r1_tarski(X1,k1_tops_1(X2,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_65]), c_0_32])])).
% 49.22/49.49  fof(c_0_91, plain, ![X42, X43]:((~v1_tops_1(X43,X42)|k2_pre_topc(X42,X43)=k2_struct_0(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X42))&(k2_pre_topc(X42,X43)!=k2_struct_0(X42)|v1_tops_1(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|~l1_pre_topc(X42))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 49.22/49.49  cnf(c_0_92, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 49.22/49.49  cnf(c_0_93, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 49.22/49.49  cnf(c_0_94, plain, (k1_tops_1(X1,k1_xboole_0)=k1_xboole_0|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_65]), c_0_32])])).
% 49.22/49.49  cnf(c_0_95, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|r1_xboole_0(X1,esk2_0)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 49.22/49.49  cnf(c_0_96, plain, (X1=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 49.22/49.49  cnf(c_0_97, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_85, c_0_44])).
% 49.22/49.49  cnf(c_0_98, plain, (m1_subset_1(k1_tops_1(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 49.22/49.49  cnf(c_0_99, negated_conjecture, (r1_xboole_0(X1,X2)|~l1_pre_topc(X3)|~r1_tarski(X1,k1_tops_1(X3,k1_xboole_0))|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_89])).
% 49.22/49.49  cnf(c_0_100, negated_conjecture, (r1_xboole_0(k1_tops_1(X1,k1_xboole_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_90, c_0_40])).
% 49.22/49.49  cnf(c_0_101, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 49.22/49.49  cnf(c_0_102, plain, (v1_tops_1(X1,X2)|~v2_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_47]), c_0_48])).
% 49.22/49.49  cnf(c_0_103, plain, (v2_tops_1(k1_xboole_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_32])])).
% 49.22/49.49  cnf(c_0_104, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)|r1_xboole_0(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_95, c_0_40])).
% 49.22/49.49  cnf(c_0_105, plain, (X1=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_xboole_0(X2,X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_96, c_0_71])).
% 49.22/49.49  cnf(c_0_106, negated_conjecture, (r1_xboole_0(esk2_0,k1_tops_1(esk1_0,k1_xboole_0))|~r1_xboole_0(k1_tops_1(esk1_0,k1_xboole_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_68])])).
% 49.22/49.49  cnf(c_0_107, negated_conjecture, (r1_xboole_0(k1_tops_1(X1,k1_xboole_0),X2)|~l1_pre_topc(X1)|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_99, c_0_40])).
% 49.22/49.49  cnf(c_0_108, negated_conjecture, (r1_tarski(k1_tops_1(X1,k1_xboole_0),esk2_0)|~l1_pre_topc(X1)|~m1_subset_1(k1_tops_1(X1,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_100]), c_0_44])])).
% 49.22/49.49  cnf(c_0_109, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_48])).
% 49.22/49.49  cnf(c_0_110, plain, (v2_tops_1(X2,X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 49.22/49.49  cnf(c_0_111, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_101, c_0_48])).
% 49.22/49.49  cnf(c_0_112, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_87]), c_0_88])]), c_0_103])).
% 49.22/49.49  cnf(c_0_113, negated_conjecture, (X1=k1_xboole_0|v2_tops_1(esk2_0,esk1_0)|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_104])).
% 49.22/49.49  cnf(c_0_114, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_47, c_0_61])).
% 49.22/49.49  cnf(c_0_115, negated_conjecture, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_xboole_0(esk2_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_105, c_0_44])).
% 49.22/49.49  cnf(c_0_116, negated_conjecture, (r1_xboole_0(esk2_0,k1_tops_1(esk1_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_68]), c_0_40])])).
% 49.22/49.49  cnf(c_0_117, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k1_xboole_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_68]), c_0_32])])).
% 49.22/49.49  cnf(c_0_118, plain, (r1_xboole_0(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_35]), c_0_32])])).
% 49.22/49.49  cnf(c_0_119, plain, (v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v1_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_47]), c_0_48])).
% 49.22/49.49  cnf(c_0_120, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),k1_xboole_0))=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_32])])).
% 49.22/49.49  cnf(c_0_121, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0|v2_tops_1(esk2_0,esk1_0)|~r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_113, c_0_40])).
% 49.22/49.49  cnf(c_0_122, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_73]), c_0_48])).
% 49.22/49.49  cnf(c_0_123, negated_conjecture, (k1_tops_1(esk1_0,k1_xboole_0)=k1_xboole_0|~m1_subset_1(k1_tops_1(esk1_0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])])).
% 49.22/49.49  cnf(c_0_124, plain, (r1_xboole_0(k3_subset_1(X1,X2),k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_118, c_0_48])).
% 49.22/49.49  cnf(c_0_125, plain, (v2_tops_1(k1_tops_1(X1,X2),X1)|~v1_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_119, c_0_61])).
% 49.22/49.49  cnf(c_0_126, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_111, c_0_92])).
% 49.22/49.49  cnf(c_0_127, plain, (m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_120]), c_0_88])])).
% 49.22/49.49  cnf(c_0_128, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)=k1_xboole_0|v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_65]), c_0_68]), c_0_44])])).
% 49.22/49.49  cnf(c_0_129, plain, (k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,k1_xboole_0))=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_120]), c_0_32])])).
% 49.22/49.49  cnf(c_0_130, negated_conjecture, (k1_tops_1(esk1_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_109]), c_0_68]), c_0_32])])).
% 49.22/49.49  fof(c_0_131, plain, ![X15, X16, X17]:(~r1_tarski(X15,k2_xboole_0(X16,X17))|~r1_xboole_0(X15,X17)|r1_tarski(X15,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 49.22/49.49  fof(c_0_132, plain, ![X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(X25))|~m1_subset_1(X27,k1_zfmisc_1(X25))|k4_subset_1(X25,X26,X27)=k2_xboole_0(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 49.22/49.49  cnf(c_0_133, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~r1_tarski(X1,k3_subset_1(X4,X3))|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_124])).
% 49.22/49.49  cnf(c_0_134, plain, (v2_tops_1(k1_tops_1(X1,X2),X1)|~v2_tops_1(X2,X1)|~v1_tops_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_127])).
% 49.22/49.49  cnf(c_0_135, negated_conjecture, (v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_128]), c_0_68]), c_0_44])])).
% 49.22/49.49  cnf(c_0_136, negated_conjecture, (k2_struct_0(esk1_0)=k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_68])])).
% 49.22/49.49  cnf(c_0_137, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_131])).
% 49.22/49.49  cnf(c_0_138, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_132])).
% 49.22/49.49  fof(c_0_139, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|~m1_subset_1(X20,k1_zfmisc_1(X18))|k4_subset_1(X18,X19,X20)=k4_subset_1(X18,X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k4_subset_1])])).
% 49.22/49.49  fof(c_0_140, plain, ![X52, X53]:(~l1_pre_topc(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|k2_pre_topc(X52,X53)=k4_subset_1(u1_struct_0(X52),X53,k2_tops_1(X52,X53)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_tops_1])])])).
% 49.22/49.49  fof(c_0_141, plain, ![X50, X51]:(~l1_pre_topc(X50)|(~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|k2_tops_1(X50,X51)=k2_tops_1(X50,k3_subset_1(u1_struct_0(X50),X51)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_tops_1])])])).
% 49.22/49.49  cnf(c_0_142, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_35]), c_0_32])])).
% 49.22/49.49  cnf(c_0_143, plain, (v1_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)|~v2_tops_1(k1_tops_1(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_102, c_0_61])).
% 49.22/49.49  cnf(c_0_144, negated_conjecture, (v2_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)|~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_44]), c_0_135]), c_0_136]), c_0_68])])).
% 49.22/49.49  cnf(c_0_145, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_130]), c_0_68]), c_0_32])])).
% 49.22/49.49  cnf(c_0_146, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k4_subset_1(X4,X2,X3))), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 49.22/49.49  cnf(c_0_147, plain, (k4_subset_1(X2,X1,X3)=k4_subset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_139])).
% 49.22/49.49  cnf(c_0_148, plain, (k2_pre_topc(X1,X2)=k4_subset_1(u1_struct_0(X1),X2,k2_tops_1(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_140])).
% 49.22/49.49  cnf(c_0_149, plain, (k2_tops_1(X1,X2)=k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_141])).
% 49.22/49.49  fof(c_0_150, plain, ![X46, X47]:(~l1_pre_topc(X46)|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))|m1_subset_1(k2_tops_1(X46,X47),k1_zfmisc_1(u1_struct_0(X46)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_1])])).
% 49.22/49.49  cnf(c_0_151, negated_conjecture, (r1_xboole_0(esk2_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_142, c_0_44])).
% 49.22/49.49  cnf(c_0_152, plain, (v1_tops_1(k2_struct_0(X1),X1)|~v2_tops_1(k1_tops_1(X1,X2),X1)|~v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_126]), c_0_127])).
% 49.22/49.49  cnf(c_0_153, negated_conjecture, (v2_tops_1(k1_tops_1(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_92]), c_0_145]), c_0_68]), c_0_32])])).
% 49.22/49.49  cnf(c_0_154, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k4_subset_1(X4,X3,X2))), inference(spm,[status(thm)],[c_0_146, c_0_147])).
% 49.22/49.49  cnf(c_0_155, plain, (k4_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),X2),k2_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_48])).
% 49.22/49.49  cnf(c_0_156, plain, (m1_subset_1(k2_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_150])).
% 49.22/49.49  cnf(c_0_157, negated_conjecture, (r1_tarski(esk2_0,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_151])).
% 49.22/49.49  cnf(c_0_158, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_44]), c_0_136]), c_0_153]), c_0_135]), c_0_68])])).
% 49.22/49.49  cnf(c_0_159, plain, (r1_tarski(X1,k2_tops_1(X2,X3))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X1,k3_subset_1(u1_struct_0(X2),X3))|~r1_tarski(X1,k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_156]), c_0_48])).
% 49.22/49.49  cnf(c_0_160, negated_conjecture, (r1_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_xboole_0(k3_subset_1(u1_struct_0(esk1_0),X1),esk2_0)), inference(spm,[status(thm)],[c_0_97, c_0_48])).
% 49.22/49.49  cnf(c_0_161, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k1_tops_1(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_157, c_0_61])).
% 49.22/49.49  cnf(c_0_162, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0))=k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_158]), c_0_136]), c_0_68]), c_0_32])])).
% 49.22/49.49  cnf(c_0_163, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)|~r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 49.22/49.49  cnf(c_0_164, plain, (r1_tarski(X1,k2_tops_1(X2,X3))|~v2_tops_1(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_xboole_0(X1,k3_subset_1(u1_struct_0(X2),X3))|~r1_tarski(X1,k2_struct_0(X2))), inference(spm,[status(thm)],[c_0_159, c_0_126])).
% 49.22/49.49  cnf(c_0_165, negated_conjecture, (r1_xboole_0(esk2_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_84]), c_0_44])])).
% 49.22/49.49  cnf(c_0_166, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_162]), c_0_68]), c_0_88]), c_0_44]), c_0_32]), c_0_130]), c_0_31])])).
% 49.22/49.49  cnf(c_0_167, negated_conjecture, (~r1_tarski(esk2_0,k2_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_163, c_0_135])])).
% 49.22/49.49  cnf(c_0_168, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164, c_0_165]), c_0_135]), c_0_68]), c_0_44]), c_0_136]), c_0_166])]), c_0_167]), ['proof']).
% 49.22/49.49  # SZS output end CNFRefutation
% 49.22/49.49  # Proof object total steps             : 169
% 49.22/49.49  # Proof object clause steps            : 122
% 49.22/49.49  # Proof object formula steps           : 47
% 49.22/49.49  # Proof object conjectures             : 49
% 49.22/49.49  # Proof object clause conjectures      : 46
% 49.22/49.49  # Proof object formula conjectures     : 3
% 49.22/49.49  # Proof object initial clauses used    : 29
% 49.22/49.49  # Proof object initial formulas used   : 23
% 49.22/49.49  # Proof object generating inferences   : 91
% 49.22/49.49  # Proof object simplifying inferences  : 117
% 49.22/49.49  # Training examples: 0 positive, 0 negative
% 49.22/49.49  # Parsed axioms                        : 24
% 49.22/49.49  # Removed by relevancy pruning/SinE    : 0
% 49.22/49.49  # Initial clauses                      : 33
% 49.22/49.49  # Removed in clause preprocessing      : 0
% 49.22/49.49  # Initial clauses in saturation        : 33
% 49.22/49.49  # Processed clauses                    : 216145
% 49.22/49.49  # ...of these trivial                  : 327
% 49.22/49.49  # ...subsumed                          : 196400
% 49.22/49.49  # ...remaining for further processing  : 19418
% 49.22/49.49  # Other redundant clauses eliminated   : 17
% 49.22/49.49  # Clauses deleted for lack of memory   : 145044
% 49.22/49.49  # Backward-subsumed                    : 2453
% 49.22/49.49  # Backward-rewritten                   : 1893
% 49.22/49.49  # Generated clauses                    : 2221701
% 49.22/49.49  # ...of the previous two non-trivial   : 2156678
% 49.22/49.49  # Contextual simplify-reflections      : 4324
% 49.22/49.49  # Paramodulations                      : 2221684
% 49.22/49.49  # Factorizations                       : 0
% 49.22/49.49  # Equation resolutions                 : 17
% 49.22/49.49  # Propositional unsat checks           : 3
% 49.22/49.49  #    Propositional check models        : 0
% 49.22/49.49  #    Propositional check unsatisfiable : 0
% 49.22/49.49  #    Propositional clauses             : 0
% 49.22/49.49  #    Propositional clauses after purity: 0
% 49.22/49.49  #    Propositional unsat core size     : 0
% 49.22/49.49  #    Propositional preprocessing time  : 0.000
% 49.22/49.49  #    Propositional encoding time       : 2.793
% 49.22/49.49  #    Propositional solver time         : 0.857
% 49.22/49.49  #    Success case prop preproc time    : 0.000
% 49.22/49.49  #    Success case prop encoding time   : 0.000
% 49.22/49.49  #    Success case prop solver time     : 0.000
% 49.22/49.49  # Current number of processed clauses  : 15038
% 49.22/49.49  #    Positive orientable unit clauses  : 181
% 49.22/49.49  #    Positive unorientable unit clauses: 2
% 49.22/49.49  #    Negative unit clauses             : 24
% 49.22/49.49  #    Non-unit-clauses                  : 14831
% 49.22/49.49  # Current number of unprocessed clauses: 987581
% 49.22/49.49  # ...number of literals in the above   : 5886665
% 49.22/49.49  # Current number of archived formulas  : 0
% 49.22/49.49  # Current number of archived clauses   : 4378
% 49.22/49.49  # Clause-clause subsumption calls (NU) : 71846879
% 49.22/49.49  # Rec. Clause-clause subsumption calls : 8550216
% 49.22/49.49  # Non-unit clause-clause subsumptions  : 116304
% 49.22/49.49  # Unit Clause-clause subsumption calls : 93733
% 49.22/49.49  # Rewrite failures with RHS unbound    : 17
% 49.22/49.49  # BW rewrite match attempts            : 410
% 49.22/49.49  # BW rewrite match successes           : 111
% 49.22/49.49  # Condensation attempts                : 0
% 49.22/49.49  # Condensation successes               : 0
% 49.22/49.49  # Termbank termtop insertions          : 131695895
% 49.30/49.57  
% 49.30/49.57  # -------------------------------------------------
% 49.30/49.57  # User time                : 48.105 s
% 49.30/49.57  # System time              : 1.029 s
% 49.30/49.57  # Total time               : 49.134 s
% 49.30/49.57  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
