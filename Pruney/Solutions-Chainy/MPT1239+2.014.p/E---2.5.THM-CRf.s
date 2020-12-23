%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:55 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 149 expanded)
%              Number of clauses        :   39 (  64 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 441 expanded)
%              Number of equality atoms :    8 (  16 expanded)
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

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

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

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tops_1])).

fof(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k7_subset_1(X21,X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

fof(c_0_15,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | r1_tarski(k1_tops_1(X26,X27),X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X24,k1_zfmisc_1(X25))
        | r1_tarski(X24,X25) )
      & ( ~ r1_tarski(X24,X25)
        | m1_subset_1(X24,k1_zfmisc_1(X25)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | ~ r1_xboole_0(X18,X20)
      | r1_tarski(X18,k4_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k1_tops_1(X1,X2),X3)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_34,plain,(
    ! [X28,X29,X30] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ r1_tarski(X29,X30)
      | r1_tarski(k1_tops_1(X28,X29),k1_tops_1(X28,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_35,plain,(
    ! [X4,X5] :
      ( ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X5,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_27]),c_0_28])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),u1_struct_0(esk1_0))
    | ~ r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28])])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

fof(c_0_43,plain,(
    ! [X16,X17] : r1_xboole_0(k4_xboole_0(X16,X17),X17) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_45,plain,(
    ! [X11,X12] : r1_tarski(k4_xboole_0(X11,X12),X11) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_46,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)
    | ~ r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_tops_1(esk1_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28]),c_0_31])]),c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( r1_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X2,esk2_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)
    | ~ r1_xboole_0(esk3_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_31]),c_0_28])])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_18]),c_0_51]),c_0_54]),c_0_31])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k1_tops_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_22]),c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_22]),c_0_62])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.48  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.48  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.48  #
% 0.19/0.48  # Preprocessing time       : 0.037 s
% 0.19/0.48  # Presaturation interreduction done
% 0.19/0.48  
% 0.19/0.48  # Proof found!
% 0.19/0.48  # SZS status Theorem
% 0.19/0.48  # SZS output start CNFRefutation
% 0.19/0.48  fof(t50_tops_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 0.19/0.48  fof(redefinition_k7_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k7_subset_1(X1,X2,X3)=k4_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 0.19/0.48  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 0.19/0.48  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.48  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.19/0.48  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.19/0.48  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.48  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 0.19/0.48  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.48  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.19/0.48  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.19/0.48  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.48  fof(c_0_12, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,k7_subset_1(u1_struct_0(X1),X2,X3)),k7_subset_1(u1_struct_0(X1),k1_tops_1(X1,X2),k1_tops_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t50_tops_1])).
% 0.19/0.48  fof(c_0_13, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.19/0.48  fof(c_0_14, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|k7_subset_1(X21,X22,X23)=k4_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).
% 0.19/0.48  fof(c_0_15, plain, ![X26, X27]:(~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|r1_tarski(k1_tops_1(X26,X27),X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.19/0.48  fof(c_0_16, plain, ![X24, X25]:((~m1_subset_1(X24,k1_zfmisc_1(X25))|r1_tarski(X24,X25))&(~r1_tarski(X24,X25)|m1_subset_1(X24,k1_zfmisc_1(X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.48  cnf(c_0_17, negated_conjecture, (~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k7_subset_1(u1_struct_0(esk1_0),k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.48  cnf(c_0_18, plain, (k7_subset_1(X2,X1,X3)=k4_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.48  fof(c_0_19, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|~r1_xboole_0(X18,X20)|r1_tarski(X18,k4_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.19/0.48  fof(c_0_20, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_xboole_0(X14,X15)|r1_xboole_0(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.19/0.48  cnf(c_0_21, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.48  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_23, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k4_xboole_0(k1_tops_1(esk1_0,esk2_0),k1_tops_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.48  cnf(c_0_24, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.48  cnf(c_0_25, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.48  cnf(c_0_26, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.48  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.48  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.48  fof(c_0_29, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.48  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.48  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.48  cnf(c_0_32, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))|~r1_xboole_0(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.48  cnf(c_0_33, plain, (r1_xboole_0(k1_tops_1(X1,X2),X3)|~l1_pre_topc(X1)|~r1_tarski(X2,u1_struct_0(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.48  fof(c_0_34, plain, ![X28, X29, X30]:(~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|(~r1_tarski(X29,X30)|r1_tarski(k1_tops_1(X28,X29),k1_tops_1(X28,X30)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.19/0.48  fof(c_0_35, plain, ![X4, X5]:(~r1_xboole_0(X4,X5)|r1_xboole_0(X5,X4)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.48  cnf(c_0_36, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_27]), c_0_28])])).
% 0.19/0.48  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.48  cnf(c_0_38, negated_conjecture, (r1_tarski(esk2_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.48  cnf(c_0_39, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k1_tops_1(esk1_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0)),k1_tops_1(esk1_0,esk2_0))|~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),u1_struct_0(esk1_0))|~r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_tops_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_28])])).
% 0.19/0.48  cnf(c_0_40, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.48  cnf(c_0_41, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.48  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k1_tops_1(esk1_0,esk3_0),X1)|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 0.19/0.48  fof(c_0_43, plain, ![X16, X17]:r1_xboole_0(k4_xboole_0(X16,X17),X17), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.19/0.48  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.48  fof(c_0_45, plain, ![X11, X12]:r1_tarski(k4_xboole_0(X11,X12),X11), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.19/0.48  fof(c_0_46, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.48  cnf(c_0_47, negated_conjecture, (~m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)|~r1_xboole_0(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_tops_1(esk1_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_28]), c_0_31])]), c_0_30])).
% 0.19/0.48  cnf(c_0_48, negated_conjecture, (r1_xboole_0(X1,k1_tops_1(esk1_0,esk3_0))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.48  cnf(c_0_49, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.48  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X2,esk2_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_44])).
% 0.19/0.48  cnf(c_0_51, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.48  cnf(c_0_52, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.48  cnf(c_0_53, negated_conjecture, (~m1_subset_1(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~r1_tarski(k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0),esk2_0)|~r1_xboole_0(esk3_0,k7_subset_1(u1_struct_0(esk1_0),esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.48  cnf(c_0_54, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_41, c_0_49])).
% 0.19/0.48  cnf(c_0_55, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k4_xboole_0(esk2_0,X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.48  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.48  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_31]), c_0_28])])).
% 0.19/0.48  cnf(c_0_58, negated_conjecture, (~m1_subset_1(k4_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))|~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_18]), c_0_51]), c_0_54]), c_0_31])])).
% 0.19/0.48  cnf(c_0_59, negated_conjecture, (r1_tarski(k4_xboole_0(esk2_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.48  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k1_tops_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_57])).
% 0.19/0.48  cnf(c_0_61, negated_conjecture, (~m1_subset_1(k1_tops_1(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_22]), c_0_59])])).
% 0.19/0.48  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_tops_1(esk1_0,esk2_0),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_60, c_0_56])).
% 0.19/0.48  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_22]), c_0_62])]), ['proof']).
% 0.19/0.48  # SZS output end CNFRefutation
% 0.19/0.48  # Proof object total steps             : 64
% 0.19/0.48  # Proof object clause steps            : 39
% 0.19/0.48  # Proof object formula steps           : 25
% 0.19/0.48  # Proof object conjectures             : 26
% 0.19/0.48  # Proof object clause conjectures      : 23
% 0.19/0.48  # Proof object formula conjectures     : 3
% 0.19/0.48  # Proof object initial clauses used    : 16
% 0.19/0.48  # Proof object initial formulas used   : 12
% 0.19/0.48  # Proof object generating inferences   : 22
% 0.19/0.48  # Proof object simplifying inferences  : 19
% 0.19/0.48  # Training examples: 0 positive, 0 negative
% 0.19/0.48  # Parsed axioms                        : 12
% 0.19/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.48  # Initial clauses                      : 19
% 0.19/0.48  # Removed in clause preprocessing      : 0
% 0.19/0.48  # Initial clauses in saturation        : 19
% 0.19/0.48  # Processed clauses                    : 801
% 0.19/0.48  # ...of these trivial                  : 4
% 0.19/0.48  # ...subsumed                          : 432
% 0.19/0.48  # ...remaining for further processing  : 365
% 0.19/0.48  # Other redundant clauses eliminated   : 2
% 0.19/0.48  # Clauses deleted for lack of memory   : 0
% 0.19/0.48  # Backward-subsumed                    : 42
% 0.19/0.48  # Backward-rewritten                   : 5
% 0.19/0.48  # Generated clauses                    : 2736
% 0.19/0.48  # ...of the previous two non-trivial   : 2416
% 0.19/0.48  # Contextual simplify-reflections      : 12
% 0.19/0.48  # Paramodulations                      : 2734
% 0.19/0.48  # Factorizations                       : 0
% 0.19/0.48  # Equation resolutions                 : 2
% 0.19/0.48  # Propositional unsat checks           : 0
% 0.19/0.48  #    Propositional check models        : 0
% 0.19/0.48  #    Propositional check unsatisfiable : 0
% 0.19/0.48  #    Propositional clauses             : 0
% 0.19/0.48  #    Propositional clauses after purity: 0
% 0.19/0.48  #    Propositional unsat core size     : 0
% 0.19/0.48  #    Propositional preprocessing time  : 0.000
% 0.19/0.48  #    Propositional encoding time       : 0.000
% 0.19/0.48  #    Propositional solver time         : 0.000
% 0.19/0.48  #    Success case prop preproc time    : 0.000
% 0.19/0.48  #    Success case prop encoding time   : 0.000
% 0.19/0.48  #    Success case prop solver time     : 0.000
% 0.19/0.48  # Current number of processed clauses  : 298
% 0.19/0.48  #    Positive orientable unit clauses  : 33
% 0.19/0.48  #    Positive unorientable unit clauses: 0
% 0.19/0.48  #    Negative unit clauses             : 14
% 0.19/0.48  #    Non-unit-clauses                  : 251
% 0.19/0.48  # Current number of unprocessed clauses: 1635
% 0.19/0.48  # ...number of literals in the above   : 5897
% 0.19/0.48  # Current number of archived formulas  : 0
% 0.19/0.48  # Current number of archived clauses   : 65
% 0.19/0.48  # Clause-clause subsumption calls (NU) : 10361
% 0.19/0.48  # Rec. Clause-clause subsumption calls : 6952
% 0.19/0.48  # Non-unit clause-clause subsumptions  : 289
% 0.19/0.48  # Unit Clause-clause subsumption calls : 285
% 0.19/0.48  # Rewrite failures with RHS unbound    : 0
% 0.19/0.48  # BW rewrite match attempts            : 10
% 0.19/0.48  # BW rewrite match successes           : 4
% 0.19/0.48  # Condensation attempts                : 0
% 0.19/0.48  # Condensation successes               : 0
% 0.19/0.48  # Termbank termtop insertions          : 39296
% 0.19/0.48  
% 0.19/0.48  # -------------------------------------------------
% 0.19/0.48  # User time                : 0.130 s
% 0.19/0.48  # System time              : 0.007 s
% 0.19/0.48  # Total time               : 0.138 s
% 0.19/0.48  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
