%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:12:15 EST 2020

% Result     : Theorem 10.91s
% Output     : CNFRefutation 10.91s
% Verified   : 
% Statistics : Number of formulae       :  207 (139581 expanded)
%              Number of clauses        :  166 (69730 expanded)
%              Number of leaves         :   20 (33893 expanded)
%              Depth                    :   43
%              Number of atoms          :  490 (376919 expanded)
%              Number of equality atoms :   66 (39155 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t36_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(k3_subset_1(X1,X2),X3)
           => r1_tarski(k3_subset_1(X1,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

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

fof(t49_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_21,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_tops_1(X2,X1)
             => v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t91_tops_1])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v3_tops_1(esk2_0,esk1_0)
    & ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_26,plain,(
    ! [X9] : m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

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

fof(c_0_28,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_subset_1(X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | ~ r1_tarski(k3_subset_1(X17,X18),X19)
      | r1_tarski(k3_subset_1(X17,X19),X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_33])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_subset_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r1_tarski(k3_subset_1(X2,X3),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(k3_subset_1(X2,X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_36])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_subset_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_subset_1(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_subset_1(k3_subset_1(esk2_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k2_subset_1(esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(k2_subset_1(k3_subset_1(esk2_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k2_subset_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

fof(c_0_55,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | r1_tarski(k1_tops_1(X39,X40),X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_56,plain,(
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

fof(c_0_57,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | k3_subset_1(X12,k3_subset_1(X12,X13)) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_54])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_62,plain,(
    ! [X41,X42] :
      ( ( ~ v2_tops_1(X42,X41)
        | k1_tops_1(X41,X42) = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) )
      & ( k1_tops_1(X41,X42) != k1_xboole_0
        | v2_tops_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).

cnf(c_0_63,plain,
    ( v2_tops_1(X2,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k3_subset_1(X2,k3_subset_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k3_subset_1(esk2_0,esk2_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_60])).

cnf(c_0_67,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_61])).

cnf(c_0_68,plain,
    ( k1_tops_1(X2,X1) = k1_xboole_0
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ v1_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)) = k3_subset_1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_46]),c_0_66])])).

cnf(c_0_71,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_72,plain,(
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

cnf(c_0_73,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ v2_tops_1(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_44])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_48])).

cnf(c_0_76,plain,
    ( v1_tops_1(X2,X1)
    | k2_pre_topc(X1,X2) != k2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_77,plain,(
    ! [X22] :
      ( ~ l1_struct_0(X22)
      | k2_struct_0(X22) = u1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_78,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_79,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | r1_tarski(X27,k2_pre_topc(X26,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_71]),c_0_75])])).

cnf(c_0_81,plain,
    ( v1_tops_1(u1_struct_0(X1),X1)
    | k2_pre_topc(X1,u1_struct_0(X1)) != k2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_44])).

cnf(c_0_82,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_83,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_24])).

cnf(c_0_85,plain,
    ( r1_tarski(X2,k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_86,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | m1_subset_1(k2_pre_topc(X23,X24),k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_46])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_60]),c_0_30]),c_0_44])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))
    | k2_struct_0(esk1_0) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_71])])).

cnf(c_0_90,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,plain,
    ( k2_pre_topc(X1,X2) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_70])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))
    | k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_71])])).

cnf(c_0_97,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_44])])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))
    | ~ r1_tarski(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k2_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_41])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_24])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_71])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_36])).

cnf(c_0_103,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_104,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_31])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k2_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k3_subset_1(esk2_0,esk2_0) = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_101]),c_0_44])])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_105]),c_0_70])).

cnf(c_0_111,negated_conjecture,
    ( k3_subset_1(esk2_0,esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108])])).

cnf(c_0_112,plain,
    ( r1_tarski(k3_subset_1(X1,X1),X2)
    | ~ m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_46])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_102,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_113])).

fof(c_0_116,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(X14))
      | ~ r1_tarski(X15,k3_subset_1(X14,X16))
      | r1_tarski(X16,k3_subset_1(X14,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).

cnf(c_0_117,plain,
    ( X1 = k3_subset_1(X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_46])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[c_0_113,c_0_111])).

cnf(c_0_120,plain,
    ( r1_tarski(X3,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_subset_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_119])])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))
    | ~ m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_43])).

cnf(c_0_123,negated_conjecture,
    ( k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0) = k3_subset_1(u1_struct_0(esk1_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_121]),c_0_44])])).

cnf(c_0_124,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_88])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_124]),c_0_119]),c_0_30])])).

fof(c_0_126,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
      | k1_tops_1(X31,X32) = k3_subset_1(u1_struct_0(X31),k2_pre_topc(X31,k3_subset_1(u1_struct_0(X31),X32))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).

cnf(c_0_127,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0
    | ~ r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_125])).

cnf(c_0_128,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_129,plain,
    ( k1_tops_1(X1,X2) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_126])).

cnf(c_0_130,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_44]),c_0_124]),c_0_30])])).

cnf(c_0_131,plain,
    ( r1_tarski(k2_subset_1(k2_subset_1(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_41])).

cnf(c_0_132,negated_conjecture,
    ( k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) = k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_130]),c_0_71]),c_0_124])])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)
    | ~ r1_tarski(k2_subset_1(X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_102])).

cnf(c_0_134,plain,
    ( r1_tarski(k2_subset_1(k2_subset_1(k2_subset_1(X1))),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_132]),c_0_71]),c_0_124])])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),k2_subset_1(k2_subset_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_137,plain,
    ( m1_subset_1(k2_subset_1(k2_subset_1(X1)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_131])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_135]),c_0_130]),c_0_124])])).

cnf(c_0_139,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,k2_subset_1(k2_subset_1(esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_136]),c_0_137]),c_0_44])])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_92]),c_0_71]),c_0_30])])).

cnf(c_0_141,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)
    | ~ r1_tarski(k3_subset_1(X1,X1),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_94]),c_0_70])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,k2_subset_1(k2_subset_1(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_139])).

cnf(c_0_143,negated_conjecture,
    ( r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_46])).

cnf(c_0_145,negated_conjecture,
    ( r1_tarski(k3_subset_1(X1,X1),esk2_0)
    | ~ m1_subset_1(k3_subset_1(esk2_0,k2_subset_1(k2_subset_1(esk2_0))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_46])).

cnf(c_0_146,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_143])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_144])).

cnf(c_0_148,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_149,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(esk2_0,esk2_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_70]),c_0_44])])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_139])])).

cnf(c_0_151,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_147,c_0_111])).

cnf(c_0_152,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_140])).

cnf(c_0_153,plain,
    ( k2_pre_topc(X2,X1) = k2_struct_0(X2)
    | ~ v1_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_154,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_71]),c_0_75])])).

cnf(c_0_155,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0)
    | ~ v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_111])).

cnf(c_0_156,plain,
    ( k3_subset_1(X1,X1) = k3_subset_1(X2,X2)
    | ~ m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_46])).

cnf(c_0_157,negated_conjecture,
    ( m1_subset_1(k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_150])).

cnf(c_0_158,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_159,plain,
    ( k2_pre_topc(X1,u1_struct_0(X1)) = k2_struct_0(X1)
    | ~ v1_tops_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_153,c_0_44])).

cnf(c_0_160,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0)
    | ~ v2_tops_1(k1_xboole_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_154,c_0_111])).

cnf(c_0_161,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0)
    | k2_struct_0(esk1_0) != k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_81]),c_0_71])])).

cnf(c_0_162,plain,
    ( r1_tarski(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_pre_topc(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_92])).

cnf(c_0_163,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_157]),c_0_111]),c_0_111]),c_0_158])])).

cnf(c_0_164,negated_conjecture,
    ( k2_struct_0(esk1_0) = k2_pre_topc(esk1_0,u1_struct_0(esk1_0))
    | ~ v2_tops_1(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_160]),c_0_71])])).

cnf(c_0_165,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0)
    | k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_90]),c_0_71])])).

cnf(c_0_166,plain,
    ( k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2)) = k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_129])).

cnf(c_0_167,plain,
    ( r1_tarski(k1_tops_1(X1,k3_subset_1(X2,X3)),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_61])).

fof(c_0_168,plain,(
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

cnf(c_0_169,plain,
    ( r1_tarski(k3_subset_1(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(X1,X2)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_162,c_0_43])).

cnf(c_0_170,negated_conjecture,
    ( k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_xboole_0) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_163]),c_0_44])])).

cnf(c_0_171,plain,
    ( k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_64]),c_0_33])).

cnf(c_0_172,negated_conjecture,
    ( k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0)
    | ~ v2_tops_1(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_164]),c_0_71])])).

cnf(c_0_173,negated_conjecture,
    ( v2_tops_1(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_97]),c_0_71])])).

cnf(c_0_174,plain,
    ( k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))) = k2_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_64]),c_0_92]),c_0_33])).

cnf(c_0_175,negated_conjecture,
    ( r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_132]),c_0_71]),c_0_124]),c_0_30])])).

cnf(c_0_176,plain,
    ( v1_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v2_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_148,c_0_129])).

cnf(c_0_177,plain,
    ( v2_tops_1(k2_pre_topc(X2,X1),X2)
    | ~ v3_tops_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_168])).

cnf(c_0_178,negated_conjecture,
    ( r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_71]),c_0_158]),c_0_30])])).

cnf(c_0_179,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k1_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_130]),c_0_71]),c_0_124])])).

cnf(c_0_180,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_181,plain,
    ( k2_pre_topc(X1,k2_pre_topc(X1,X2)) = k2_struct_0(X1)
    | ~ v1_tops_1(k2_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_153,c_0_92])).

cnf(c_0_182,negated_conjecture,
    ( k2_pre_topc(esk1_0,u1_struct_0(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_172,c_0_173])])).

cnf(c_0_183,negated_conjecture,
    ( v1_tops_1(u1_struct_0(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160,c_0_173])])).

fof(c_0_184,plain,(
    ! [X28,X29,X30] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ r1_tarski(X29,X30)
      | r1_tarski(k2_pre_topc(X28,X29),k2_pre_topc(X28,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).

cnf(c_0_185,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_153,c_0_33])).

cnf(c_0_186,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))) = k2_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174,c_0_132]),c_0_71]),c_0_30])])).

cnf(c_0_187,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_175])).

cnf(c_0_188,plain,
    ( v1_tops_1(k1_tops_1(X1,X2),X1)
    | ~ v3_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_177]),c_0_33])).

cnf(c_0_189,negated_conjecture,
    ( v3_tops_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_190,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_178])).

cnf(c_0_191,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_179])).

cnf(c_0_192,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_179])).

cnf(c_0_193,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != k2_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_124]),c_0_71])]),c_0_180])).

cnf(c_0_194,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_182]),c_0_182]),c_0_183]),c_0_71]),c_0_44])])).

cnf(c_0_195,plain,
    ( r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_184])).

cnf(c_0_196,plain,
    ( k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)) = k2_struct_0(X1)
    | ~ v2_tops_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_185,c_0_148])).

cnf(c_0_197,negated_conjecture,
    ( v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_186]),c_0_71]),c_0_187])])).

cnf(c_0_198,negated_conjecture,
    ( v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_130]),c_0_132]),c_0_189]),c_0_71]),c_0_190]),c_0_124])])).

cnf(c_0_199,plain,
    ( k3_subset_1(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,k3_subset_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_200,negated_conjecture,
    ( k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0)) = k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191,c_0_92]),c_0_71]),c_0_124])])).

cnf(c_0_201,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_92]),c_0_71]),c_0_124])])).

cnf(c_0_202,negated_conjecture,
    ( k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)) != u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_193,c_0_194])).

cnf(c_0_203,plain,
    ( r1_tarski(k2_struct_0(X1),k2_pre_topc(X1,X2))
    | ~ v2_tops_1(X3,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(X1),X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195,c_0_196]),c_0_33])).

cnf(c_0_204,negated_conjecture,
    ( v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_197,c_0_198])])).

cnf(c_0_205,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_200]),c_0_201])]),c_0_202])).

cnf(c_0_206,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_135]),c_0_194]),c_0_204]),c_0_71]),c_0_124]),c_0_190])]),c_0_205]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:09:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 10.91/11.07  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 10.91/11.07  # and selection function SelectComplexExceptUniqMaxHorn.
% 10.91/11.07  #
% 10.91/11.07  # Preprocessing time       : 0.028 s
% 10.91/11.07  # Presaturation interreduction done
% 10.91/11.07  
% 10.91/11.07  # Proof found!
% 10.91/11.07  # SZS status Theorem
% 10.91/11.07  # SZS output start CNFRefutation
% 10.91/11.07  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.91/11.07  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.91/11.07  fof(t91_tops_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 10.91/11.07  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 10.91/11.07  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.91/11.07  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.91/11.07  fof(t36_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(k3_subset_1(X1,X2),X3)=>r1_tarski(k3_subset_1(X1,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 10.91/11.07  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 10.91/11.07  fof(d4_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_1)).
% 10.91/11.07  fof(involutiveness_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,k3_subset_1(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.91/11.07  fof(t84_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tops_1(X2,X1)<=>k1_tops_1(X1,X2)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tops_1)).
% 10.91/11.07  fof(d3_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v1_tops_1(X2,X1)<=>k2_pre_topc(X1,X2)=k2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 10.91/11.07  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 10.91/11.07  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.91/11.07  fof(t48_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(X2,k2_pre_topc(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 10.91/11.07  fof(dt_k2_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 10.91/11.07  fof(t35_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X3))=>r1_tarski(X3,k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 10.91/11.07  fof(d1_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 10.91/11.07  fof(d5_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)<=>v2_tops_1(k2_pre_topc(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 10.91/11.07  fof(t49_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 10.91/11.07  fof(c_0_20, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 10.91/11.07  fof(c_0_21, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 10.91/11.07  fof(c_0_22, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_tops_1(X2,X1)=>v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1))))), inference(assume_negation,[status(cth)],[t91_tops_1])).
% 10.91/11.07  cnf(c_0_23, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 10.91/11.07  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 10.91/11.07  fof(c_0_25, negated_conjecture, (l1_pre_topc(esk1_0)&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(v3_tops_1(esk2_0,esk1_0)&~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 10.91/11.07  fof(c_0_26, plain, ![X9]:m1_subset_1(k2_subset_1(X9),k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 10.91/11.07  fof(c_0_27, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 10.91/11.07  fof(c_0_28, plain, ![X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(X10))|m1_subset_1(k3_subset_1(X10,X11),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 10.91/11.07  cnf(c_0_29, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 10.91/11.07  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 10.91/11.07  cnf(c_0_31, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 10.91/11.07  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.91/11.07  cnf(c_0_33, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 10.91/11.07  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 10.91/11.07  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_subset_1(X2))), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 10.91/11.07  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 10.91/11.07  fof(c_0_37, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|(~m1_subset_1(X19,k1_zfmisc_1(X17))|(~r1_tarski(k3_subset_1(X17,X18),X19)|r1_tarski(k3_subset_1(X17,X19),X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t36_subset_1])])])).
% 10.91/11.07  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(spm,[status(thm)],[c_0_29, c_0_33])).
% 10.91/11.07  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 10.91/11.07  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 10.91/11.07  cnf(c_0_41, plain, (r1_tarski(k2_subset_1(X1),X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 10.91/11.07  cnf(c_0_42, plain, (r1_tarski(k3_subset_1(X2,X3),X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(k3_subset_1(X2,X1),X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 10.91/11.07  cnf(c_0_43, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_36])).
% 10.91/11.07  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_36])).
% 10.91/11.07  cnf(c_0_45, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_subset_1(esk2_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 10.91/11.07  cnf(c_0_46, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 10.91/11.07  cnf(c_0_47, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),u1_struct_0(esk1_0))|~m1_subset_1(k2_subset_1(esk2_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 10.91/11.07  cnf(c_0_48, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_47, c_0_31])).
% 10.91/11.07  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_48])).
% 10.91/11.07  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_subset_1(k3_subset_1(esk2_0,esk2_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_49, c_0_41])).
% 10.91/11.07  cnf(c_0_51, negated_conjecture, (r1_tarski(k2_subset_1(esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 10.91/11.07  cnf(c_0_52, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(k2_subset_1(X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_46])).
% 10.91/11.07  cnf(c_0_53, negated_conjecture, (m1_subset_1(k2_subset_1(k3_subset_1(esk2_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_50])).
% 10.91/11.07  cnf(c_0_54, negated_conjecture, (m1_subset_1(k2_subset_1(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 10.91/11.07  fof(c_0_55, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))|r1_tarski(k1_tops_1(X39,X40),X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 10.91/11.07  fof(c_0_56, plain, ![X35, X36]:((~v2_tops_1(X36,X35)|v1_tops_1(k3_subset_1(u1_struct_0(X35),X36),X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))&(~v1_tops_1(k3_subset_1(u1_struct_0(X35),X36),X35)|v2_tops_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_pre_topc(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_1])])])])).
% 10.91/11.07  fof(c_0_57, plain, ![X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|k3_subset_1(X12,k3_subset_1(X12,X13))=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_subset_1])])).
% 10.91/11.07  cnf(c_0_58, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 10.91/11.07  cnf(c_0_59, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 10.91/11.07  cnf(c_0_60, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_54])).
% 10.91/11.07  cnf(c_0_61, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 10.91/11.07  fof(c_0_62, plain, ![X41, X42]:((~v2_tops_1(X42,X41)|k1_tops_1(X41,X42)=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))&(k1_tops_1(X41,X42)!=k1_xboole_0|v2_tops_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))|~l1_pre_topc(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t84_tops_1])])])])).
% 10.91/11.07  cnf(c_0_63, plain, (v2_tops_1(X2,X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 10.91/11.07  cnf(c_0_64, plain, (k3_subset_1(X2,k3_subset_1(X2,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 10.91/11.07  cnf(c_0_65, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k3_subset_1(esk2_0,esk2_0)|~r1_tarski(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 10.91/11.07  cnf(c_0_66, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_60])).
% 10.91/11.07  cnf(c_0_67, plain, (m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_39, c_0_61])).
% 10.91/11.07  cnf(c_0_68, plain, (k1_tops_1(X2,X1)=k1_xboole_0|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 10.91/11.07  cnf(c_0_69, plain, (v2_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~v1_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_33])).
% 10.91/11.07  cnf(c_0_70, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))=k3_subset_1(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_46]), c_0_66])])).
% 10.91/11.07  cnf(c_0_71, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 10.91/11.07  fof(c_0_72, plain, ![X33, X34]:((~v1_tops_1(X34,X33)|k2_pre_topc(X33,X34)=k2_struct_0(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))&(k2_pre_topc(X33,X34)!=k2_struct_0(X33)|v1_tops_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|~l1_pre_topc(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tops_1])])])])).
% 10.91/11.07  cnf(c_0_73, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~v2_tops_1(X1,X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 10.91/11.07  cnf(c_0_74, negated_conjecture, (v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_44])])).
% 10.91/11.07  cnf(c_0_75, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_48])).
% 10.91/11.07  cnf(c_0_76, plain, (v1_tops_1(X2,X1)|k2_pre_topc(X1,X2)!=k2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 10.91/11.07  fof(c_0_77, plain, ![X22]:(~l1_struct_0(X22)|k2_struct_0(X22)=u1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 10.91/11.07  fof(c_0_78, plain, ![X25]:(~l1_pre_topc(X25)|l1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 10.91/11.07  fof(c_0_79, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|r1_tarski(X27,k2_pre_topc(X26,X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_pre_topc])])])).
% 10.91/11.07  cnf(c_0_80, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_71]), c_0_75])])).
% 10.91/11.07  cnf(c_0_81, plain, (v1_tops_1(u1_struct_0(X1),X1)|k2_pre_topc(X1,u1_struct_0(X1))!=k2_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_76, c_0_44])).
% 10.91/11.07  cnf(c_0_82, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 10.91/11.07  cnf(c_0_83, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 10.91/11.07  cnf(c_0_84, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_24])).
% 10.91/11.07  cnf(c_0_85, plain, (r1_tarski(X2,k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 10.91/11.07  fof(c_0_86, plain, ![X23, X24]:(~l1_pre_topc(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|m1_subset_1(k2_pre_topc(X23,X24),k1_zfmisc_1(u1_struct_0(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).
% 10.91/11.07  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X3))), inference(spm,[status(thm)],[c_0_23, c_0_46])).
% 10.91/11.07  cnf(c_0_88, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_60]), c_0_30]), c_0_44])])).
% 10.91/11.07  cnf(c_0_89, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))|k2_struct_0(esk1_0)!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_71])])).
% 10.91/11.07  cnf(c_0_90, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 10.91/11.07  cnf(c_0_91, plain, (k2_pre_topc(X1,X2)=X2|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 10.91/11.07  cnf(c_0_92, plain, (m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 10.91/11.07  cnf(c_0_93, negated_conjecture, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_87, c_0_70])).
% 10.91/11.07  cnf(c_0_94, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 10.91/11.07  cnf(c_0_95, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_88])).
% 10.91/11.07  cnf(c_0_96, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))|k2_pre_topc(esk1_0,u1_struct_0(esk1_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_71])])).
% 10.91/11.07  cnf(c_0_97, plain, (k2_pre_topc(X1,u1_struct_0(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_44])])).
% 10.91/11.07  cnf(c_0_98, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(esk2_0,esk2_0))|~r1_tarski(X2,esk2_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 10.91/11.07  cnf(c_0_99, negated_conjecture, (r1_tarski(k2_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_95, c_0_41])).
% 10.91/11.07  cnf(c_0_100, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_84, c_0_24])).
% 10.91/11.07  cnf(c_0_101, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_71])])).
% 10.91/11.07  cnf(c_0_102, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_98, c_0_36])).
% 10.91/11.07  cnf(c_0_103, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 10.91/11.07  cnf(c_0_104, plain, (r1_tarski(k3_subset_1(X1,X1),X1)), inference(spm,[status(thm)],[c_0_52, c_0_31])).
% 10.91/11.07  cnf(c_0_105, negated_conjecture, (m1_subset_1(k2_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_99])).
% 10.91/11.07  cnf(c_0_106, negated_conjecture, (k3_subset_1(esk2_0,esk2_0)=k1_xboole_0|~m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 10.91/11.07  cnf(c_0_107, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_102])).
% 10.91/11.07  cnf(c_0_108, negated_conjecture, (r1_tarski(k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_101]), c_0_44])])).
% 10.91/11.07  cnf(c_0_109, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_23, c_0_104])).
% 10.91/11.07  cnf(c_0_110, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_105]), c_0_70])).
% 10.91/11.07  cnf(c_0_111, negated_conjecture, (k3_subset_1(esk2_0,esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108])])).
% 10.91/11.07  cnf(c_0_112, plain, (r1_tarski(k3_subset_1(X1,X1),X2)|~m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_109, c_0_46])).
% 10.91/11.07  cnf(c_0_113, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_39, c_0_110])).
% 10.91/11.07  cnf(c_0_114, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,esk2_0)), inference(rw,[status(thm)],[c_0_102, c_0_111])).
% 10.91/11.07  cnf(c_0_115, negated_conjecture, (r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_112, c_0_113])).
% 10.91/11.07  fof(c_0_116, plain, ![X14, X15, X16]:(~m1_subset_1(X15,k1_zfmisc_1(X14))|(~m1_subset_1(X16,k1_zfmisc_1(X14))|(~r1_tarski(X15,k3_subset_1(X14,X16))|r1_tarski(X16,k3_subset_1(X14,X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_subset_1])])])).
% 10.91/11.07  cnf(c_0_117, plain, (X1=k3_subset_1(X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X2))), inference(spm,[status(thm)],[c_0_58, c_0_46])).
% 10.91/11.07  cnf(c_0_118, negated_conjecture, (r1_tarski(k1_xboole_0,k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(spm,[status(thm)],[c_0_114, c_0_115])).
% 10.91/11.07  cnf(c_0_119, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(rw,[status(thm)],[c_0_113, c_0_111])).
% 10.91/11.07  cnf(c_0_120, plain, (r1_tarski(X3,k3_subset_1(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_subset_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 10.91/11.07  cnf(c_0_121, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_119])])).
% 10.91/11.07  cnf(c_0_122, plain, (r1_tarski(X1,k3_subset_1(X2,k3_subset_1(k3_subset_1(X2,X1),X3)))|~m1_subset_1(k3_subset_1(k3_subset_1(X2,X1),X3),k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(k3_subset_1(X2,X1)))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_120, c_0_43])).
% 10.91/11.07  cnf(c_0_123, negated_conjecture, (k3_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_xboole_0)=k3_subset_1(u1_struct_0(esk1_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_121]), c_0_44])])).
% 10.91/11.07  cnf(c_0_124, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_88])).
% 10.91/11.07  cnf(c_0_125, negated_conjecture, (r1_tarski(esk2_0,k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_124]), c_0_119]), c_0_30])])).
% 10.91/11.07  fof(c_0_126, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|k1_tops_1(X31,X32)=k3_subset_1(u1_struct_0(X31),k2_pre_topc(X31,k3_subset_1(u1_struct_0(X31),X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_1])])])).
% 10.91/11.07  cnf(c_0_127, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0|~r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0)),esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_125])).
% 10.91/11.07  cnf(c_0_128, plain, (r1_tarski(k3_subset_1(X1,X2),X3)|~m1_subset_1(k3_subset_1(X1,X3),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_42, c_0_24])).
% 10.91/11.07  cnf(c_0_129, plain, (k1_tops_1(X1,X2)=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_126])).
% 10.91/11.07  cnf(c_0_130, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_128]), c_0_44]), c_0_124]), c_0_30])])).
% 10.91/11.07  cnf(c_0_131, plain, (r1_tarski(k2_subset_1(k2_subset_1(X1)),X1)), inference(spm,[status(thm)],[c_0_35, c_0_41])).
% 10.91/11.07  cnf(c_0_132, negated_conjecture, (k1_tops_1(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))=k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_130]), c_0_71]), c_0_124])])).
% 10.91/11.07  cnf(c_0_133, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)|~r1_tarski(k2_subset_1(X1),esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_102])).
% 10.91/11.07  cnf(c_0_134, plain, (r1_tarski(k2_subset_1(k2_subset_1(k2_subset_1(X1))),X1)), inference(spm,[status(thm)],[c_0_35, c_0_131])).
% 10.91/11.07  cnf(c_0_135, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_132]), c_0_71]), c_0_124])])).
% 10.91/11.07  cnf(c_0_136, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),k2_subset_1(k2_subset_1(esk2_0)))), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 10.91/11.07  cnf(c_0_137, plain, (m1_subset_1(k2_subset_1(k2_subset_1(X1)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_131])).
% 10.91/11.07  cnf(c_0_138, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))|~m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_135]), c_0_130]), c_0_124])])).
% 10.91/11.07  cnf(c_0_139, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,k2_subset_1(k2_subset_1(esk2_0))),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_136]), c_0_137]), c_0_44])])).
% 10.91/11.07  cnf(c_0_140, negated_conjecture, (r1_tarski(esk2_0,k2_pre_topc(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_92]), c_0_71]), c_0_30])])).
% 10.91/11.07  cnf(c_0_141, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)|~r1_tarski(k3_subset_1(X1,X1),esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_94]), c_0_70])).
% 10.91/11.07  cnf(c_0_142, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,k3_subset_1(esk2_0,k2_subset_1(k2_subset_1(esk2_0))))), inference(spm,[status(thm)],[c_0_23, c_0_139])).
% 10.91/11.07  cnf(c_0_143, negated_conjecture, (r1_tarski(X1,k2_pre_topc(esk1_0,esk2_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_23, c_0_140])).
% 10.91/11.07  cnf(c_0_144, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_141, c_0_46])).
% 10.91/11.07  cnf(c_0_145, negated_conjecture, (r1_tarski(k3_subset_1(X1,X1),esk2_0)|~m1_subset_1(k3_subset_1(esk2_0,k2_subset_1(k2_subset_1(esk2_0))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_142, c_0_46])).
% 10.91/11.07  cnf(c_0_146, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_143])).
% 10.91/11.07  cnf(c_0_147, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk2_0),k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_144])).
% 10.91/11.07  cnf(c_0_148, plain, (v1_tops_1(k3_subset_1(u1_struct_0(X2),X1),X2)|~v2_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 10.91/11.07  cnf(c_0_149, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(esk2_0,esk2_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_70]), c_0_44])])).
% 10.91/11.07  cnf(c_0_150, negated_conjecture, (r1_tarski(k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_139])])).
% 10.91/11.07  cnf(c_0_151, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))|~m1_subset_1(esk2_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_147, c_0_111])).
% 10.91/11.07  cnf(c_0_152, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_39, c_0_140])).
% 10.91/11.07  cnf(c_0_153, plain, (k2_pre_topc(X2,X1)=k2_struct_0(X2)|~v1_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 10.91/11.07  cnf(c_0_154, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)|~v2_tops_1(k3_subset_1(esk2_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_71]), c_0_75])])).
% 10.91/11.07  cnf(c_0_155, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)|~v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(rw,[status(thm)],[c_0_74, c_0_111])).
% 10.91/11.07  cnf(c_0_156, plain, (k3_subset_1(X1,X1)=k3_subset_1(X2,X2)|~m1_subset_1(k3_subset_1(X1,X1),k1_zfmisc_1(X2))|~m1_subset_1(k3_subset_1(X2,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_117, c_0_46])).
% 10.91/11.07  cnf(c_0_157, negated_conjecture, (m1_subset_1(k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_150])).
% 10.91/11.07  cnf(c_0_158, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_pre_topc(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_151, c_0_152])).
% 10.91/11.07  cnf(c_0_159, plain, (k2_pre_topc(X1,u1_struct_0(X1))=k2_struct_0(X1)|~v1_tops_1(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_153, c_0_44])).
% 10.91/11.07  cnf(c_0_160, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)|~v2_tops_1(k1_xboole_0,esk1_0)), inference(rw,[status(thm)],[c_0_154, c_0_111])).
% 10.91/11.07  cnf(c_0_161, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)|k2_struct_0(esk1_0)!=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155, c_0_81]), c_0_71])])).
% 10.91/11.07  cnf(c_0_162, plain, (r1_tarski(X1,u1_struct_0(X2))|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_pre_topc(X2,X3))), inference(spm,[status(thm)],[c_0_29, c_0_92])).
% 10.91/11.07  cnf(c_0_163, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k2_pre_topc(esk1_0,esk2_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_157]), c_0_111]), c_0_111]), c_0_158])])).
% 10.91/11.07  cnf(c_0_164, negated_conjecture, (k2_struct_0(esk1_0)=k2_pre_topc(esk1_0,u1_struct_0(esk1_0))|~v2_tops_1(k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159, c_0_160]), c_0_71])])).
% 10.91/11.07  cnf(c_0_165, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)|k2_pre_topc(esk1_0,u1_struct_0(esk1_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161, c_0_90]), c_0_71])])).
% 10.91/11.07  cnf(c_0_166, plain, (k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2))=k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_64, c_0_129])).
% 10.91/11.07  cnf(c_0_167, plain, (r1_tarski(k1_tops_1(X1,k3_subset_1(X2,X3)),X2)|~l1_pre_topc(X1)|~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_38, c_0_61])).
% 10.91/11.07  fof(c_0_168, plain, ![X37, X38]:((~v3_tops_1(X38,X37)|v2_tops_1(k2_pre_topc(X37,X38),X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_pre_topc(X37))&(~v2_tops_1(k2_pre_topc(X37,X38),X37)|v3_tops_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|~l1_pre_topc(X37))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_1])])])])).
% 10.91/11.07  cnf(c_0_169, plain, (r1_tarski(k3_subset_1(k2_pre_topc(X1,X2),X3),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(X1,X2)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_162, c_0_43])).
% 10.91/11.07  cnf(c_0_170, negated_conjecture, (k3_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_xboole_0)=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_163]), c_0_44])])).
% 10.91/11.07  cnf(c_0_171, plain, (k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2))=k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_129, c_0_64]), c_0_33])).
% 10.91/11.07  cnf(c_0_172, negated_conjecture, (k2_pre_topc(esk1_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)|~v2_tops_1(k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_164]), c_0_71])])).
% 10.91/11.07  cnf(c_0_173, negated_conjecture, (v2_tops_1(k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165, c_0_97]), c_0_71])])).
% 10.91/11.07  cnf(c_0_174, plain, (k3_subset_1(u1_struct_0(X1),k1_tops_1(X1,k3_subset_1(u1_struct_0(X1),X2)))=k2_pre_topc(X1,X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_64]), c_0_92]), c_0_33])).
% 10.91/11.07  cnf(c_0_175, negated_conjecture, (r1_tarski(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167, c_0_132]), c_0_71]), c_0_124]), c_0_30])])).
% 10.91/11.07  cnf(c_0_176, plain, (v1_tops_1(k1_tops_1(X1,X2),X1)|~v2_tops_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_148, c_0_129])).
% 10.91/11.07  cnf(c_0_177, plain, (v2_tops_1(k2_pre_topc(X2,X1),X2)|~v3_tops_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_168])).
% 10.91/11.07  cnf(c_0_178, negated_conjecture, (r1_tarski(k2_pre_topc(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_170]), c_0_71]), c_0_158]), c_0_30])])).
% 10.91/11.07  cnf(c_0_179, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))=k1_tops_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_130]), c_0_71]), c_0_124])])).
% 10.91/11.07  cnf(c_0_180, negated_conjecture, (~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 10.91/11.07  cnf(c_0_181, plain, (k2_pre_topc(X1,k2_pre_topc(X1,X2))=k2_struct_0(X1)|~v1_tops_1(k2_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_153, c_0_92])).
% 10.91/11.07  cnf(c_0_182, negated_conjecture, (k2_pre_topc(esk1_0,u1_struct_0(esk1_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_172, c_0_173])])).
% 10.91/11.07  cnf(c_0_183, negated_conjecture, (v1_tops_1(u1_struct_0(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_160, c_0_173])])).
% 10.91/11.07  fof(c_0_184, plain, ![X28, X29, X30]:(~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|(~r1_tarski(X29,X30)|r1_tarski(k2_pre_topc(X28,X29),k2_pre_topc(X28,X30)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_pre_topc])])])).
% 10.91/11.07  cnf(c_0_185, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~v1_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_153, c_0_33])).
% 10.91/11.07  cnf(c_0_186, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)))=k2_pre_topc(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_174, c_0_132]), c_0_71]), c_0_30])])).
% 10.91/11.07  cnf(c_0_187, negated_conjecture, (m1_subset_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_175])).
% 10.91/11.07  cnf(c_0_188, plain, (v1_tops_1(k1_tops_1(X1,X2),X1)|~v3_tops_1(k3_subset_1(u1_struct_0(X1),X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_176, c_0_177]), c_0_33])).
% 10.91/11.07  cnf(c_0_189, negated_conjecture, (v3_tops_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 10.91/11.07  cnf(c_0_190, negated_conjecture, (m1_subset_1(k2_pre_topc(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_178])).
% 10.91/11.07  cnf(c_0_191, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))|~m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_64, c_0_179])).
% 10.91/11.07  cnf(c_0_192, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_33, c_0_179])).
% 10.91/11.07  cnf(c_0_193, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=k2_struct_0(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_124]), c_0_71])]), c_0_180])).
% 10.91/11.07  cnf(c_0_194, negated_conjecture, (k2_struct_0(esk1_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_181, c_0_182]), c_0_182]), c_0_183]), c_0_71]), c_0_44])])).
% 10.91/11.07  cnf(c_0_195, plain, (r1_tarski(k2_pre_topc(X1,X2),k2_pre_topc(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_184])).
% 10.91/11.07  cnf(c_0_196, plain, (k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))=k2_struct_0(X1)|~v2_tops_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_185, c_0_148])).
% 10.91/11.07  cnf(c_0_197, negated_conjecture, (v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)|~v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_186]), c_0_71]), c_0_187])])).
% 10.91/11.07  cnf(c_0_198, negated_conjecture, (v1_tops_1(k3_subset_1(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,esk2_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_130]), c_0_132]), c_0_189]), c_0_71]), c_0_190]), c_0_124])])).
% 10.91/11.07  cnf(c_0_199, plain, (k3_subset_1(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,k3_subset_1(X1,X2))), inference(spm,[status(thm)],[c_0_58, c_0_43])).
% 10.91/11.07  cnf(c_0_200, negated_conjecture, (k3_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0))=k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_191, c_0_92]), c_0_71]), c_0_124])])).
% 10.91/11.07  cnf(c_0_201, negated_conjecture, (m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_92]), c_0_71]), c_0_124])])).
% 10.91/11.07  cnf(c_0_202, negated_conjecture, (k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))!=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_193, c_0_194])).
% 10.91/11.07  cnf(c_0_203, plain, (r1_tarski(k2_struct_0(X1),k2_pre_topc(X1,X2))|~v2_tops_1(X3,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(k3_subset_1(u1_struct_0(X1),X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_195, c_0_196]), c_0_33])).
% 10.91/11.07  cnf(c_0_204, negated_conjecture, (v2_tops_1(k2_pre_topc(esk1_0,esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_197, c_0_198])])).
% 10.91/11.07  cnf(c_0_205, negated_conjecture, (~r1_tarski(u1_struct_0(esk1_0),k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199, c_0_200]), c_0_201])]), c_0_202])).
% 10.91/11.07  cnf(c_0_206, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_135]), c_0_194]), c_0_204]), c_0_71]), c_0_124]), c_0_190])]), c_0_205]), ['proof']).
% 10.91/11.07  # SZS output end CNFRefutation
% 10.91/11.07  # Proof object total steps             : 207
% 10.91/11.07  # Proof object clause steps            : 166
% 10.91/11.07  # Proof object formula steps           : 41
% 10.91/11.07  # Proof object conjectures             : 102
% 10.91/11.07  # Proof object clause conjectures      : 99
% 10.91/11.07  # Proof object formula conjectures     : 3
% 10.91/11.07  # Proof object initial clauses used    : 27
% 10.91/11.07  # Proof object initial formulas used   : 20
% 10.91/11.07  # Proof object generating inferences   : 129
% 10.91/11.07  # Proof object simplifying inferences  : 143
% 10.91/11.07  # Training examples: 0 positive, 0 negative
% 10.91/11.07  # Parsed axioms                        : 20
% 10.91/11.07  # Removed by relevancy pruning/SinE    : 0
% 10.91/11.07  # Initial clauses                      : 30
% 10.91/11.07  # Removed in clause preprocessing      : 0
% 10.91/11.07  # Initial clauses in saturation        : 30
% 10.91/11.07  # Processed clauses                    : 93825
% 10.91/11.07  # ...of these trivial                  : 526
% 10.91/11.07  # ...subsumed                          : 85771
% 10.91/11.07  # ...remaining for further processing  : 7528
% 10.91/11.07  # Other redundant clauses eliminated   : 2
% 10.91/11.07  # Clauses deleted for lack of memory   : 0
% 10.91/11.07  # Backward-subsumed                    : 266
% 10.91/11.07  # Backward-rewritten                   : 351
% 10.91/11.07  # Generated clauses                    : 874455
% 10.91/11.07  # ...of the previous two non-trivial   : 785951
% 10.91/11.07  # Contextual simplify-reflections      : 338
% 10.91/11.07  # Paramodulations                      : 874453
% 10.91/11.07  # Factorizations                       : 0
% 10.91/11.07  # Equation resolutions                 : 2
% 10.91/11.07  # Propositional unsat checks           : 1
% 10.91/11.07  #    Propositional check models        : 0
% 10.91/11.07  #    Propositional check unsatisfiable : 0
% 10.91/11.07  #    Propositional clauses             : 0
% 10.91/11.07  #    Propositional clauses after purity: 0
% 10.91/11.07  #    Propositional unsat core size     : 0
% 10.91/11.07  #    Propositional preprocessing time  : 0.000
% 10.91/11.07  #    Propositional encoding time       : 0.480
% 10.91/11.07  #    Propositional solver time         : 0.169
% 10.91/11.07  #    Success case prop preproc time    : 0.000
% 10.91/11.07  #    Success case prop encoding time   : 0.000
% 10.91/11.07  #    Success case prop solver time     : 0.000
% 10.91/11.07  # Current number of processed clauses  : 6880
% 10.91/11.07  #    Positive orientable unit clauses  : 512
% 10.91/11.07  #    Positive unorientable unit clauses: 0
% 10.91/11.07  #    Negative unit clauses             : 126
% 10.91/11.07  #    Non-unit-clauses                  : 6242
% 10.91/11.07  # Current number of unprocessed clauses: 689074
% 10.91/11.07  # ...number of literals in the above   : 3160701
% 10.91/11.07  # Current number of archived formulas  : 0
% 10.91/11.07  # Current number of archived clauses   : 646
% 10.91/11.07  # Clause-clause subsumption calls (NU) : 5384739
% 10.91/11.07  # Rec. Clause-clause subsumption calls : 1990969
% 10.91/11.07  # Non-unit clause-clause subsumptions  : 30745
% 10.91/11.07  # Unit Clause-clause subsumption calls : 30405
% 10.91/11.07  # Rewrite failures with RHS unbound    : 0
% 10.91/11.07  # BW rewrite match attempts            : 12271
% 10.91/11.07  # BW rewrite match successes           : 71
% 10.91/11.07  # Condensation attempts                : 0
% 10.91/11.07  # Condensation successes               : 0
% 10.91/11.07  # Termbank termtop insertions          : 28948034
% 10.91/11.10  
% 10.91/11.10  # -------------------------------------------------
% 10.91/11.10  # User time                : 10.352 s
% 10.91/11.10  # System time              : 0.414 s
% 10.91/11.10  # Total time               : 10.767 s
% 10.91/11.10  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
