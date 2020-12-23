%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:57 EST 2020

% Result     : Theorem 54.20s
% Output     : CNFRefutation 54.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 168 expanded)
%              Number of clauses        :   43 (  77 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 487 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_tops_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | r1_tarski(k1_tops_1(X22,X23),X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,plain,(
    ! [X9,X10] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_23,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_xboole_0(X14,X16)
      | r1_tarski(X14,k4_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_24,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | r1_xboole_0(X11,k4_xboole_0(X13,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_32,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | k7_subset_1(X17,X18,X19) = k4_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r1_tarski(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_38])).

fof(c_0_44,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ r1_tarski(X25,X26)
      | r1_tarski(k1_tops_1(X24,X25),k1_tops_1(X24,X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1) = k4_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_15])).

cnf(c_0_47,plain,
    ( k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(X1,esk3_0)) = k1_tops_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1) = k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(X1,k4_xboole_0(X3,esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),X1)
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,esk3_0)),k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,esk3_0)),X2)
    | ~ r1_tarski(k4_xboole_0(X1,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(X2,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))
    | ~ r1_tarski(X2,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_40]),c_0_17])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_18]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 54.20/54.44  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S050I
% 54.20/54.44  # and selection function PSelectNewComplexExceptUniqMaxHorn.
% 54.20/54.44  #
% 54.20/54.44  # Preprocessing time       : 0.027 s
% 54.20/54.44  # Presaturation interreduction done
% 54.20/54.44  
% 54.20/54.44  # Proof found!
% 54.20/54.44  # SZS status Theorem
% 54.20/54.44  # SZS output start CNFRefutation
% 54.20/54.44  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 54.20/54.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 54.20/54.44  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 54.20/54.44  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 54.20/54.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 54.20/54.44  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 54.20/54.44  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 54.20/54.44  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 54.20/54.44  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 54.20/54.44  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 54.20/54.44  fof(c_0_10, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 54.20/54.44  fof(c_0_11, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 54.20/54.44  fof(c_0_12, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 54.20/54.44  fof(c_0_13, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 54.20/54.44  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 54.20/54.44  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 54.20/54.44  fof(c_0_16, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|r1_tarski(k1_tops_1(X22,X23),X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 54.20/54.44  cnf(c_0_17, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 54.20/54.44  cnf(c_0_18, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 54.20/54.44  cnf(c_0_19, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 54.20/54.44  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 54.20/54.44  fof(c_0_21, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 54.20/54.44  fof(c_0_22, plain, ![X9, X10]:r1_tarski(k4_xboole_0(X9,X10),X9), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 54.20/54.44  fof(c_0_23, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_xboole_0(X14,X16)|r1_tarski(X14,k4_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 54.20/54.44  fof(c_0_24, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|r1_xboole_0(X11,k4_xboole_0(X13,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 54.20/54.44  cnf(c_0_25, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 54.20/54.44  cnf(c_0_26, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 54.20/54.44  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 54.20/54.44  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 54.20/54.44  cnf(c_0_29, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 54.20/54.44  cnf(c_0_30, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 54.20/54.44  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 54.20/54.44  fof(c_0_32, plain, ![X17, X18, X19]:(~m1_subset_1(X18,k1_zfmisc_1(X17))|k7_subset_1(X17,X18,X19)=k4_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 54.20/54.44  cnf(c_0_33, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 54.20/54.44  cnf(c_0_34, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_15])).
% 54.20/54.44  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=X1|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 54.20/54.44  cnf(c_0_36, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)))|~r1_tarski(X1,X2)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 54.20/54.44  cnf(c_0_37, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 54.20/54.44  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 54.20/54.44  cnf(c_0_39, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 54.20/54.44  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 54.20/54.44  cnf(c_0_41, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 54.20/54.44  cnf(c_0_42, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|~r1_tarski(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 54.20/54.44  cnf(c_0_43, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_38])).
% 54.20/54.44  fof(c_0_44, plain, ![X24, X25, X26]:(~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(~r1_tarski(X25,X26)|r1_tarski(k1_tops_1(X24,X25),k1_tops_1(X24,X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 54.20/54.44  cnf(c_0_45, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 54.20/54.44  cnf(c_0_46, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),esk2_0,X1)=k4_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_15])).
% 54.20/54.44  cnf(c_0_47, plain, (k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 54.20/54.44  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_41, c_0_37])).
% 54.20/54.44  cnf(c_0_49, negated_conjecture, (k4_xboole_0(k1_tops_1(esk1_0,esk3_0),k4_xboole_0(X1,esk3_0))=k1_tops_1(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 54.20/54.44  cnf(c_0_50, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 54.20/54.44  cnf(c_0_51, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 54.20/54.44  cnf(c_0_52, negated_conjecture, (k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),X1)=k4_xboole_0(k1_tops_1(esk1_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 54.20/54.44  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(X1,k4_xboole_0(X3,esk3_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_36, c_0_49])).
% 54.20/54.44  cnf(c_0_54, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),X1)|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_26, c_0_40])).
% 54.20/54.44  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 54.20/54.44  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_20])).
% 54.20/54.44  cnf(c_0_57, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 54.20/54.44  cnf(c_0_58, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,esk3_0)),k4_xboole_0(X2,k1_tops_1(esk1_0,esk3_0)))|~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(X1,esk3_0)),X2)|~r1_tarski(k4_xboole_0(X1,esk3_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 54.20/54.44  cnf(c_0_59, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_37])).
% 54.20/54.44  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(X2,u1_struct_0(esk1_0))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_40])).
% 54.20/54.44  cnf(c_0_61, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k4_xboole_0(esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 54.20/54.44  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,X1),k1_tops_1(esk1_0,X2))|~r1_tarski(X2,u1_struct_0(esk1_0))|~r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_40]), c_0_17])).
% 54.20/54.44  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_18]), c_0_28])]), ['proof']).
% 54.20/54.44  # SZS output end CNFRefutation
% 54.20/54.44  # Proof object total steps             : 64
% 54.20/54.44  # Proof object clause steps            : 43
% 54.20/54.44  # Proof object formula steps           : 21
% 54.20/54.44  # Proof object conjectures             : 30
% 54.20/54.44  # Proof object clause conjectures      : 27
% 54.20/54.44  # Proof object formula conjectures     : 3
% 54.20/54.44  # Proof object initial clauses used    : 15
% 54.20/54.44  # Proof object initial formulas used   : 10
% 54.20/54.44  # Proof object generating inferences   : 25
% 54.20/54.44  # Proof object simplifying inferences  : 11
% 54.20/54.44  # Training examples: 0 positive, 0 negative
% 54.20/54.44  # Parsed axioms                        : 10
% 54.20/54.44  # Removed by relevancy pruning/SinE    : 0
% 54.20/54.44  # Initial clauses                      : 17
% 54.20/54.44  # Removed in clause preprocessing      : 0
% 54.20/54.44  # Initial clauses in saturation        : 17
% 54.20/54.44  # Processed clauses                    : 145461
% 54.20/54.44  # ...of these trivial                  : 2135
% 54.20/54.44  # ...subsumed                          : 126811
% 54.20/54.44  # ...remaining for further processing  : 16515
% 54.20/54.44  # Other redundant clauses eliminated   : 2
% 54.20/54.44  # Clauses deleted for lack of memory   : 89252
% 54.20/54.44  # Backward-subsumed                    : 994
% 54.20/54.44  # Backward-rewritten                   : 167
% 54.20/54.44  # Generated clauses                    : 5495786
% 54.20/54.44  # ...of the previous two non-trivial   : 4980100
% 54.20/54.44  # Contextual simplify-reflections      : 203
% 54.20/54.44  # Paramodulations                      : 5495784
% 54.20/54.44  # Factorizations                       : 0
% 54.20/54.44  # Equation resolutions                 : 2
% 54.20/54.44  # Propositional unsat checks           : 0
% 54.20/54.44  #    Propositional check models        : 0
% 54.20/54.44  #    Propositional check unsatisfiable : 0
% 54.20/54.44  #    Propositional clauses             : 0
% 54.20/54.44  #    Propositional clauses after purity: 0
% 54.20/54.44  #    Propositional unsat core size     : 0
% 54.20/54.44  #    Propositional preprocessing time  : 0.000
% 54.20/54.44  #    Propositional encoding time       : 0.000
% 54.20/54.44  #    Propositional solver time         : 0.000
% 54.20/54.44  #    Success case prop preproc time    : 0.000
% 54.20/54.44  #    Success case prop encoding time   : 0.000
% 54.20/54.44  #    Success case prop solver time     : 0.000
% 54.20/54.44  # Current number of processed clauses  : 15336
% 54.20/54.44  #    Positive orientable unit clauses  : 1694
% 54.20/54.44  #    Positive unorientable unit clauses: 0
% 54.20/54.44  #    Negative unit clauses             : 6
% 54.20/54.44  #    Non-unit-clauses                  : 13636
% 54.20/54.45  # Current number of unprocessed clauses: 2352178
% 54.20/54.45  # ...number of literals in the above   : 8074519
% 54.20/54.45  # Current number of archived formulas  : 0
% 54.20/54.45  # Current number of archived clauses   : 1177
% 54.20/54.45  # Clause-clause subsumption calls (NU) : 23751723
% 54.20/54.45  # Rec. Clause-clause subsumption calls : 15254721
% 54.20/54.45  # Non-unit clause-clause subsumptions  : 127990
% 54.20/54.45  # Unit Clause-clause subsumption calls : 140603
% 54.20/54.45  # Rewrite failures with RHS unbound    : 0
% 54.20/54.45  # BW rewrite match attempts            : 39239
% 54.20/54.45  # BW rewrite match successes           : 119
% 54.20/54.45  # Condensation attempts                : 0
% 54.20/54.45  # Condensation successes               : 0
% 54.20/54.45  # Termbank termtop insertions          : 170194810
% 54.31/54.52  
% 54.31/54.52  # -------------------------------------------------
% 54.31/54.52  # User time                : 53.097 s
% 54.31/54.52  # System time              : 1.036 s
% 54.31/54.52  # Total time               : 54.133 s
% 54.31/54.52  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
