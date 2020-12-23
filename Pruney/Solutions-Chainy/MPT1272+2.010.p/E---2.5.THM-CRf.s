%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 (15795 expanded)
%              Number of clauses        :  120 (7899 expanded)
%              Number of leaves         :   22 (3883 expanded)
%              Depth                    :   35
%              Number of atoms          :  412 (40064 expanded)
%              Number of equality atoms :   60 (7551 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t91_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
           => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(t22_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(t39_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(k3_subset_1(X1,X2),X2)
      <=> X2 = k2_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(t36_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(d4_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(involutiveness_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,k3_subset_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t84_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tops_1(X2,X1)
          <=> k1_tops_1(X1,X2) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(d3_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_tops_1(X2,X1)
          <=> k2_pre_topc(X1,X2) = k2_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t48_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(X2,k2_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t35_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,k3_subset_1(X1,X3))
           => r1_tarski(X3,k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(d1_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(d5_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_tops_1(X2,X1)
          <=> v2_tops_1(k2_pre_topc(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

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

fof(c_0_22,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_23,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_26,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

fof(c_0_27,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tops_1(X2,X1)
             => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_tops_1])).

fof(c_0_29,plain,(
    ! [X9] : m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_30,plain,(
    ! [X14] : k2_subset_1(X14) = k3_subset_1(X14,k1_subset_1(X14)) ),
    inference(variable_rename,[status(thm)],[t22_subset_1])).

fof(c_0_31,plain,(
    ! [X21,X22] :
      ( ( ~ r1_tarski(k3_subset_1(X21,X22),X22)
        | X22 = k2_subset_1(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) )
      & ( X22 != k2_subset_1(X21)
        | r1_tarski(k3_subset_1(X21,X22),X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_subset_1])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_tops_1(esk2_0,esk1_0)
    & ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k2_subset_1(X1) = k3_subset_1(X1,k1_subset_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_subset_1(X2,X1),X1)
    | X1 != k2_subset_1(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( X2 = k2_subset_1(X1)
    | ~ r1_tarski(k3_subset_1(X1,X2),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( m1_subset_1(k3_subset_1(X1,k1_subset_1(X1)),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_subset_1(X2,X1),X1)
    | X1 != k3_subset_1(X2,k1_subset_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_46,plain,
    ( X2 = k3_subset_1(X1,k1_subset_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,k1_subset_1(X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_subset_1(X1,k3_subset_1(X1,k1_subset_1(X1))),k3_subset_1(X1,k1_subset_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_45]),c_0_44])])).

cnf(c_0_52,plain,
    ( k3_subset_1(X1,k1_subset_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_49])).

cnf(c_0_54,plain,
    ( r1_tarski(k3_subset_1(X1,k1_subset_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_41])).

fof(c_0_55,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ m1_subset_1(X20,k1_zfmisc_1(X18))
      | ~ r1_tarski(k3_subset_1(X18,X19),X20)
      | r1_tarski(k3_subset_1(X18,X20),X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).

cnf(c_0_56,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,k1_subset_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( r1_tarski(k3_subset_1(X2,X3),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,k3_subset_1(esk2_0,k1_subset_1(esk2_0))),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_51])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_56])).

cnf(c_0_62,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_47]),c_0_48])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(esk2_0,esk2_0),k3_subset_1(esk2_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_66,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k3_subset_1(k3_subset_1(esk2_0,esk2_0),k3_subset_1(esk2_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_64])).

fof(c_0_69,plain,(
    ! [X35,X36] :
      ( ( ~ v2_tops_1(X36,X35)
        | v1_tops_1(k3_subset_1(u1_struct_0(X35),X36),X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X35) )
      & ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X35),X36),X35)
        | v2_tops_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).

fof(c_0_70,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,k3_subset_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_71,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_25])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_68])).

cnf(c_0_74,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k3_subset_1(esk2_0,esk2_0)
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_62])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_73])).

fof(c_0_79,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | r1_tarski(k1_tops_1(X39,X40),X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_80,plain,(
    ! [X44,X45] :
      ( ( ~ v2_tops_1(X45,X44)
        | k1_tops_1(X44,X45) = k1_xboole_0
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) )
      & ( k1_tops_1(X44,X45) != k1_xboole_0
        | v2_tops_1(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_81,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_33])).

cnf(c_0_82,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k3_subset_1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_83,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_84,plain,(
    ! [X33,X34] :
      ( ( ~ v1_tops_1(X34,X33)
        | k2_pre_topc(X33,X34) = k2_struct_0(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) )
      & ( k2_pre_topc(X33,X34) != k2_struct_0(X33)
        | v1_tops_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_86,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_48])])).

cnf(c_0_88,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_89,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(esk2_0,esk2_0)) = k1_xboole_0
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_83]),c_0_68])])).

cnf(c_0_91,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_33])).

cnf(c_0_92,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(esk2_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_82]),c_0_48])])).

fof(c_0_93,plain,(
    ! [X25] :
      ( ~ l1_struct_0(X25)
      | k2_struct_0(X25) = u1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_94,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_95,plain,(
    ! [X29,X30] :
      ( ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | r1_tarski(X30,k2_pre_topc(X29,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_73]),c_0_43]),c_0_48])])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_83]),c_0_68])])).

cnf(c_0_98,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0)
    | k2_struct_0(esk1_0) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_83]),c_0_68])])).

cnf(c_0_99,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_100,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_101,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

fof(c_0_102,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))
    | k2_struct_0(esk1_0) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_105,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_106,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_101])).

cnf(c_0_107,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_62])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_56])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))
    | k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_83])])).

cnf(c_0_111,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_48])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_82])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_109])).

cnf(c_0_115,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_25])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_83])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_114]),c_0_82])).

cnf(c_0_119,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_25])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_48])])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_25])).

cnf(c_0_122,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( k3_subset_1(esk2_0,esk2_0) = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_119,c_0_116])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_116])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( k3_subset_1(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_77]),c_0_124])])).

fof(c_0_128,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
      | ~ r1_tarski(X16,k3_subset_1(X15,X17))
      | r1_tarski(X17,k3_subset_1(X15,X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

cnf(c_0_129,plain,
    ( X1 = k3_subset_1(X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_62])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[c_0_122,c_0_127])).

cnf(c_0_132,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

cnf(c_0_133,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_131])])).

cnf(c_0_134,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))
    | ~ m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_47])).

cnf(c_0_135,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_133]),c_0_48])])).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_96])).

fof(c_0_137,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | k1_tops_1(X31,X32) = k3_subset_1(u1_struct_0(X31),k2_pre_topc(X31,k3_subset_1(u1_struct_0(X31),X32))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136]),c_0_131]),c_0_43])])).

cnf(c_0_139,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_137])).

cnf(c_0_140,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_138])).

cnf(c_0_141,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_25])).

cnf(c_0_142,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_75]),c_0_33])).

cnf(c_0_143,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_48]),c_0_136]),c_0_43])])).

cnf(c_0_144,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_83]),c_0_136])])).

fof(c_0_145,plain,(
    ! [X37,X38] :
      ( ( ~ v3_tops_1(X38,X37)
        | v2_tops_1(k2_pre_topc(X37,X38),X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_pre_topc(X37) )
      & ( ~ v2_tops_1(k2_pre_topc(X37,X38),X37)
        | v3_tops_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).

cnf(c_0_146,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_127])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_144])).

cnf(c_0_148,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_149,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_150,plain,(
    ! [X41,X42,X43] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
      | ~ r1_tarski(X42,X43)
      | r1_tarski(k1_tops_1(X41,X42),k1_tops_1(X41,X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_151,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_145])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_146])).

cnf(c_0_153,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_107]),c_0_83]),c_0_136])])).

cnf(c_0_154,negated_conjecture,
    ( ~ v2_tops_1(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_83]),c_0_43])])).

cnf(c_0_155,plain,
    ( v2_tops_1(X2,X1)
    | k1_tops_1(X1,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_156,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_150])).

cnf(c_0_157,plain,
    ( k1_tops_1(X1,k2_pre_topc(X1,X2)) = k1_xboole_0
    | ~ v3_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_151]),c_0_107])).

cnf(c_0_158,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_152,c_0_153])).

cnf(c_0_159,negated_conjecture,
    ( k1_tops_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154,c_0_155]),c_0_83]),c_0_43])])).

cnf(c_0_160,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_xboole_0)
    | ~ v3_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,k2_pre_topc(X1,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_107])).

cnf(c_0_161,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_158]),c_0_159])).

cnf(c_0_162,negated_conjecture,
    ( ~ v3_tops_1(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_43]),c_0_83])]),c_0_161])).

cnf(c_0_163,negated_conjecture,
    ( v3_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_164,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_101]),c_0_163]),c_0_43]),c_0_83])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 21:01:27 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.54  #
% 0.20/0.54  # Preprocessing time       : 0.029 s
% 0.20/0.54  # Presaturation interreduction done
% 0.20/0.54  
% 0.20/0.54  # Proof found!
% 0.20/0.54  # SZS status Theorem
% 0.20/0.54  # SZS output start CNFRefutation
% 0.20/0.54  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.54  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.54  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.54  fof(t91_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 0.20/0.54  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.54  fof(t22_subset_1, axiom, ![X1]:k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 0.20/0.54  fof(t39_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X2)<=>X2=k2_subset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 0.20/0.54  fof(t36_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 0.20/0.54  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 0.20/0.54  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 0.20/0.54  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.20/0.54  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 0.20/0.54  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 0.20/0.54  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.54  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.54  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 0.20/0.54  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 0.20/0.54  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 0.20/0.54  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 0.20/0.54  fof(d5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)<=>v2_tops_1(k2_pre_topc(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 0.20/0.54  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.20/0.54  fof(c_0_22, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.54  fof(c_0_23, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.54  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.54  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  fof(c_0_26, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.54  fof(c_0_27, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.54  fof(c_0_28, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t91_tops_1])).
% 0.20/0.54  fof(c_0_29, plain, ![X9]:m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.54  fof(c_0_30, plain, ![X14]:k2_subset_1(X14)=k3_subset_1(X14,k1_subset_1(X14)), inference(variable_rename,[status(thm)],[t22_subset_1])).
% 0.20/0.54  fof(c_0_31, plain, ![X21, X22]:((~r1_tarski(k3_subset_1(X21,X22),X22)|X22=k2_subset_1(X21)|~m1_subset_1(X22,k1_zfmisc_1(X21)))&(X22!=k2_subset_1(X21)|r1_tarski(k3_subset_1(X21,X22),X22)|~m1_subset_1(X22,k1_zfmisc_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_subset_1])])])).
% 0.20/0.54  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.54  cnf(c_0_33, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.54  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.54  fof(c_0_35, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v3_tops_1(esk2_0,esk1_0)&~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.20/0.54  cnf(c_0_36, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.54  cnf(c_0_37, plain, (k2_subset_1(X1)=k3_subset_1(X1,k1_subset_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.54  cnf(c_0_38, plain, (r1_tarski(k3_subset_1(X2,X1),X1)|X1!=k2_subset_1(X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.54  cnf(c_0_39, plain, (X2=k2_subset_1(X1)|~r1_tarski(k3_subset_1(X1,X2),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.54  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.54  cnf(c_0_41, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.54  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.54  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.54  cnf(c_0_44, plain, (m1_subset_1(k3_subset_1(X1,k1_subset_1(X1)),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.54  cnf(c_0_45, plain, (r1_tarski(k3_subset_1(X2,X1),X1)|X1!=k3_subset_1(X2,k1_subset_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_38, c_0_37])).
% 0.20/0.54  cnf(c_0_46, plain, (X2=k3_subset_1(X1,k1_subset_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X2)), inference(rw,[status(thm)],[c_0_39, c_0_37])).
% 0.20/0.54  cnf(c_0_47, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.54  cnf(c_0_48, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_41])).
% 0.20/0.54  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_43])).
% 0.20/0.54  cnf(c_0_50, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,k1_subset_1(X2)))), inference(spm,[status(thm)],[c_0_32, c_0_44])).
% 0.20/0.54  cnf(c_0_51, plain, (r1_tarski(k3_subset_1(X1,k3_subset_1(X1,k1_subset_1(X1))),k3_subset_1(X1,k1_subset_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_45]), c_0_44])])).
% 0.20/0.54  cnf(c_0_52, plain, (k3_subset_1(X1,k1_subset_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.20/0.54  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_24, c_0_49])).
% 0.20/0.54  cnf(c_0_54, plain, (r1_tarski(k3_subset_1(X1,k1_subset_1(X1)),X1)), inference(spm,[status(thm)],[c_0_50, c_0_41])).
% 0.20/0.54  fof(c_0_55, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~m1_subset_1(X20,k1_zfmisc_1(X18))|(~r1_tarski(k3_subset_1(X18,X19),X20)|r1_tarski(k3_subset_1(X18,X20),X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).
% 0.20/0.54  cnf(c_0_56, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_52])).
% 0.20/0.54  cnf(c_0_57, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k3_subset_1(esk2_0,k1_subset_1(esk2_0)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.54  cnf(c_0_58, plain, (r1_tarski(k3_subset_1(X2,X3),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.54  cnf(c_0_59, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_53, c_0_56])).
% 0.20/0.54  cnf(c_0_60, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,k3_subset_1(esk2_0,k1_subset_1(esk2_0))),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_57, c_0_51])).
% 0.20/0.54  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_24, c_0_56])).
% 0.20/0.54  cnf(c_0_62, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_47]), c_0_48])])).
% 0.20/0.54  cnf(c_0_63, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(esk2_0,esk2_0),k3_subset_1(esk2_0,esk2_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_59, c_0_56])).
% 0.20/0.54  cnf(c_0_64, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),u1_struct_0(esk1_0))), inference(rw,[status(thm)],[c_0_60, c_0_52])).
% 0.20/0.54  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.54  cnf(c_0_66, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.54  cnf(c_0_67, negated_conjecture, (m1_subset_1(k3_subset_1(k3_subset_1(esk2_0,esk2_0),k3_subset_1(esk2_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_63])).
% 0.20/0.54  cnf(c_0_68, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_64])).
% 0.20/0.54  fof(c_0_69, plain, ![X35, X36]:((~v2_tops_1(X36,X35)|v1_tops_1(k3_subset_1(u1_struct_0(X35),X36),X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))&(~v1_tops_1(k3_subset_1(u1_struct_0(X35),X36),X35)|v2_tops_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 0.20/0.54  fof(c_0_70, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,k3_subset_1(X12,X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 0.20/0.54  cnf(c_0_71, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_65, c_0_25])).
% 0.20/0.54  cnf(c_0_72, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.54  cnf(c_0_73, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_66, c_0_68])).
% 0.20/0.54  cnf(c_0_74, plain, (v2_tops_1(X2,X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.54  cnf(c_0_75, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.54  cnf(c_0_76, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k3_subset_1(esk2_0,esk2_0)|~m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.54  cnf(c_0_77, plain, (m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_62])).
% 0.20/0.54  cnf(c_0_78, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_73])).
% 0.20/0.54  fof(c_0_79, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|r1_tarski(k1_tops_1(X39,X40),X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.20/0.54  fof(c_0_80, plain, ![X44, X45]:((~v2_tops_1(X45,X44)|k1_tops_1(X44,X45)=k1_xboole_0|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))&(k1_tops_1(X44,X45)!=k1_xboole_0|v2_tops_1(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))|~l1_pre_topc(X44))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 0.20/0.54  cnf(c_0_81, plain, (v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v1_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_33])).
% 0.20/0.54  cnf(c_0_82, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k3_subset_1(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.20/0.54  cnf(c_0_83, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.54  fof(c_0_84, plain, ![X33, X34]:((~v1_tops_1(X34,X33)|k2_pre_topc(X33,X34)=k2_struct_0(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))&(k2_pre_topc(X33,X34)!=k2_struct_0(X33)|v1_tops_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 0.20/0.54  cnf(c_0_85, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.54  cnf(c_0_86, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.54  cnf(c_0_87, negated_conjecture, (v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_48])])).
% 0.20/0.54  cnf(c_0_88, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.54  cnf(c_0_89, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_42, c_0_85])).
% 0.20/0.54  cnf(c_0_90, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(esk2_0,esk2_0))=k1_xboole_0|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_83]), c_0_68])])).
% 0.20/0.54  cnf(c_0_91, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))!=k2_struct_0(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_88, c_0_33])).
% 0.20/0.54  cnf(c_0_92, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(esk2_0,esk2_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_82]), c_0_48])])).
% 0.20/0.54  fof(c_0_93, plain, ![X25]:(~l1_struct_0(X25)|k2_struct_0(X25)=u1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.54  fof(c_0_94, plain, ![X28]:(~l1_pre_topc(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.54  fof(c_0_95, plain, ![X29, X30]:(~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|r1_tarski(X30,k2_pre_topc(X29,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 0.20/0.54  cnf(c_0_96, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_73]), c_0_43]), c_0_48])])).
% 0.20/0.54  cnf(c_0_97, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_83]), c_0_68])])).
% 0.20/0.54  cnf(c_0_98, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)|k2_struct_0(esk1_0)!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_83]), c_0_68])])).
% 0.20/0.54  cnf(c_0_99, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.20/0.54  cnf(c_0_100, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.20/0.54  cnf(c_0_101, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.54  fof(c_0_102, plain, ![X26, X27]:(~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|m1_subset_1(k2_pre_topc(X26,X27),k1_zfmisc_1(u1_struct_0(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 0.20/0.54  cnf(c_0_103, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_96])).
% 0.20/0.54  cnf(c_0_104, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))|k2_struct_0(esk1_0)!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.54  cnf(c_0_105, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.20/0.54  cnf(c_0_106, plain, (k2_pre_topc(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_71, c_0_101])).
% 0.20/0.54  cnf(c_0_107, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.20/0.54  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X3))), inference(spm,[status(thm)],[c_0_24, c_0_62])).
% 0.20/0.54  cnf(c_0_109, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_103, c_0_56])).
% 0.20/0.54  cnf(c_0_110, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))|k2_pre_topc(esk1_0,u1_struct_0(esk1_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_83])])).
% 0.20/0.54  cnf(c_0_111, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_48])])).
% 0.20/0.54  cnf(c_0_112, negated_conjecture, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_108, c_0_82])).
% 0.20/0.54  cnf(c_0_113, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.20/0.54  cnf(c_0_114, negated_conjecture, (m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_109])).
% 0.20/0.54  cnf(c_0_115, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_40, c_0_25])).
% 0.20/0.54  cnf(c_0_116, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_83])])).
% 0.20/0.54  cnf(c_0_117, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 0.20/0.54  cnf(c_0_118, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_114]), c_0_82])).
% 0.20/0.54  cnf(c_0_119, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_71, c_0_25])).
% 0.20/0.54  cnf(c_0_120, negated_conjecture, (r1_tarski(k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_48])])).
% 0.20/0.54  cnf(c_0_121, negated_conjecture, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_117, c_0_25])).
% 0.20/0.54  cnf(c_0_122, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_118])).
% 0.20/0.54  cnf(c_0_123, negated_conjecture, (k3_subset_1(esk2_0,esk2_0)=k1_xboole_0|~m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_119, c_0_116])).
% 0.20/0.54  cnf(c_0_124, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_120])).
% 0.20/0.54  cnf(c_0_125, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_121, c_0_116])).
% 0.20/0.54  cnf(c_0_126, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_66, c_0_122])).
% 0.20/0.54  cnf(c_0_127, negated_conjecture, (k3_subset_1(esk2_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_77]), c_0_124])])).
% 0.20/0.54  fof(c_0_128, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|(~m1_subset_1(X17,k1_zfmisc_1(X15))|(~r1_tarski(X16,k3_subset_1(X15,X17))|r1_tarski(X17,k3_subset_1(X15,X16))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 0.20/0.54  cnf(c_0_129, plain, (X1=k3_subset_1(X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_65, c_0_62])).
% 0.20/0.54  cnf(c_0_130, negated_conjecture, (r1_tarski(k1_xboole_0,k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.20/0.54  cnf(c_0_131, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(rw,[status(thm)],[c_0_122, c_0_127])).
% 0.20/0.54  cnf(c_0_132, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_128])).
% 0.20/0.54  cnf(c_0_133, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_131])])).
% 0.20/0.54  cnf(c_0_134, plain, (r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))|~m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_132, c_0_47])).
% 0.20/0.54  cnf(c_0_135, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_133]), c_0_48])])).
% 0.20/0.54  cnf(c_0_136, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_42, c_0_96])).
% 0.20/0.54  fof(c_0_137, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|k1_tops_1(X31,X32)=k3_subset_1(u1_struct_0(X31),k2_pre_topc(X31,k3_subset_1(u1_struct_0(X31),X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 0.20/0.54  cnf(c_0_138, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_136]), c_0_131]), c_0_43])])).
% 0.20/0.54  cnf(c_0_139, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_137])).
% 0.20/0.54  cnf(c_0_140, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0|~r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_65, c_0_138])).
% 0.20/0.54  cnf(c_0_141, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_25])).
% 0.20/0.54  cnf(c_0_142, plain, (k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_75]), c_0_33])).
% 0.20/0.54  cnf(c_0_143, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_48]), c_0_136]), c_0_43])])).
% 0.20/0.54  cnf(c_0_144, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_83]), c_0_136])])).
% 0.20/0.54  fof(c_0_145, plain, ![X37, X38]:((~v3_tops_1(X38,X37)|v2_tops_1(k2_pre_topc(X37,X38),X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_pre_topc(X37))&(~v2_tops_1(k2_pre_topc(X37,X38),X37)|v3_tops_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_pre_topc(X37))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).
% 0.20/0.54  cnf(c_0_146, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_127])).
% 0.20/0.54  cnf(c_0_147, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_33, c_0_144])).
% 0.20/0.54  cnf(c_0_148, negated_conjecture, (~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.54  cnf(c_0_149, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.54  fof(c_0_150, plain, ![X41, X42, X43]:(~l1_pre_topc(X41)|(~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|(~r1_tarski(X42,X43)|r1_tarski(k1_tops_1(X41,X42),k1_tops_1(X41,X43)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.20/0.54  cnf(c_0_151, plain, (v2_tops_1(k2_pre_topc(X2,X1),X2)|~v3_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_145])).
% 0.20/0.54  cnf(c_0_152, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_62, c_0_146])).
% 0.20/0.54  cnf(c_0_153, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_107]), c_0_83]), c_0_136])])).
% 0.20/0.54  cnf(c_0_154, negated_conjecture, (~v2_tops_1(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_83]), c_0_43])])).
% 0.20/0.54  cnf(c_0_155, plain, (v2_tops_1(X2,X1)|k1_tops_1(X1,X2)!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.54  cnf(c_0_156, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_150])).
% 0.20/0.54  cnf(c_0_157, plain, (k1_tops_1(X1,k2_pre_topc(X1,X2))=k1_xboole_0|~v3_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_151]), c_0_107])).
% 0.20/0.54  cnf(c_0_158, negated_conjecture, (r1_tarski(k1_xboole_0,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_152, c_0_153])).
% 0.20/0.54  cnf(c_0_159, negated_conjecture, (k1_tops_1(esk1_0,esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_154, c_0_155]), c_0_83]), c_0_43])])).
% 0.20/0.54  cnf(c_0_160, plain, (r1_tarski(k1_tops_1(X1,X2),k1_xboole_0)|~v3_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,k2_pre_topc(X1,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_157]), c_0_107])).
% 0.20/0.54  cnf(c_0_161, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,esk2_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_158]), c_0_159])).
% 0.20/0.54  cnf(c_0_162, negated_conjecture, (~v3_tops_1(X1,esk1_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(esk2_0,k2_pre_topc(esk1_0,X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_43]), c_0_83])]), c_0_161])).
% 0.20/0.54  cnf(c_0_163, negated_conjecture, (v3_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.54  cnf(c_0_164, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_101]), c_0_163]), c_0_43]), c_0_83])]), ['proof']).
% 0.20/0.54  # SZS output end CNFRefutation
% 0.20/0.54  # Proof object total steps             : 165
% 0.20/0.54  # Proof object clause steps            : 120
% 0.20/0.54  # Proof object formula steps           : 45
% 0.20/0.54  # Proof object conjectures             : 64
% 0.20/0.54  # Proof object clause conjectures      : 61
% 0.20/0.54  # Proof object formula conjectures     : 3
% 0.20/0.54  # Proof object initial clauses used    : 30
% 0.20/0.54  # Proof object initial formulas used   : 22
% 0.20/0.54  # Proof object generating inferences   : 81
% 0.20/0.54  # Proof object simplifying inferences  : 82
% 0.20/0.54  # Training examples: 0 positive, 0 negative
% 0.20/0.54  # Parsed axioms                        : 22
% 0.20/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.54  # Initial clauses                      : 33
% 0.20/0.54  # Removed in clause preprocessing      : 1
% 0.20/0.54  # Initial clauses in saturation        : 32
% 0.20/0.54  # Processed clauses                    : 2593
% 0.20/0.54  # ...of these trivial                  : 32
% 0.20/0.54  # ...subsumed                          : 1821
% 0.20/0.54  # ...remaining for further processing  : 740
% 0.20/0.54  # Other redundant clauses eliminated   : 3
% 0.20/0.54  # Clauses deleted for lack of memory   : 0
% 0.20/0.54  # Backward-subsumed                    : 26
% 0.20/0.54  # Backward-rewritten                   : 115
% 0.20/0.54  # Generated clauses                    : 9404
% 0.20/0.54  # ...of the previous two non-trivial   : 7986
% 0.20/0.54  # Contextual simplify-reflections      : 25
% 0.20/0.54  # Paramodulations                      : 9401
% 0.20/0.54  # Factorizations                       : 0
% 0.20/0.54  # Equation resolutions                 : 3
% 0.20/0.54  # Propositional unsat checks           : 0
% 0.20/0.54  #    Propositional check models        : 0
% 0.20/0.54  #    Propositional check unsatisfiable : 0
% 0.20/0.54  #    Propositional clauses             : 0
% 0.20/0.54  #    Propositional clauses after purity: 0
% 0.20/0.54  #    Propositional unsat core size     : 0
% 0.20/0.54  #    Propositional preprocessing time  : 0.000
% 0.20/0.54  #    Propositional encoding time       : 0.000
% 0.20/0.54  #    Propositional solver time         : 0.000
% 0.20/0.54  #    Success case prop preproc time    : 0.000
% 0.20/0.54  #    Success case prop encoding time   : 0.000
% 0.20/0.54  #    Success case prop solver time     : 0.000
% 0.20/0.54  # Current number of processed clauses  : 565
% 0.20/0.54  #    Positive orientable unit clauses  : 62
% 0.20/0.54  #    Positive unorientable unit clauses: 0
% 0.20/0.54  #    Negative unit clauses             : 24
% 0.20/0.54  #    Non-unit-clauses                  : 479
% 0.20/0.54  # Current number of unprocessed clauses: 5186
% 0.20/0.54  # ...number of literals in the above   : 20074
% 0.20/0.54  # Current number of archived formulas  : 0
% 0.20/0.54  # Current number of archived clauses   : 173
% 0.20/0.54  # Clause-clause subsumption calls (NU) : 46651
% 0.20/0.54  # Rec. Clause-clause subsumption calls : 35941
% 0.20/0.54  # Non-unit clause-clause subsumptions  : 1392
% 0.20/0.54  # Unit Clause-clause subsumption calls : 900
% 0.20/0.54  # Rewrite failures with RHS unbound    : 0
% 0.20/0.54  # BW rewrite match attempts            : 52
% 0.20/0.54  # BW rewrite match successes           : 22
% 0.20/0.54  # Condensation attempts                : 0
% 0.20/0.54  # Condensation successes               : 0
% 0.20/0.54  # Termbank termtop insertions          : 166380
% 0.20/0.54  
% 0.20/0.54  # -------------------------------------------------
% 0.20/0.54  # User time                : 0.188 s
% 0.20/0.54  # System time              : 0.011 s
% 0.20/0.54  # Total time               : 0.198 s
% 0.20/0.54  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
