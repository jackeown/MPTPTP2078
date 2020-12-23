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
% DateTime   : Thu Dec  3 11:13:03 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 769 expanded)
%              Number of clauses        :   55 ( 365 expanded)
%              Number of leaves         :    9 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 (3825 expanded)
%              Number of equality atoms :   39 ( 828 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t20_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( v1_tops_2(X2,X1)
                  & v1_tops_2(X3,X1) )
               => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tops_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_11,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( ( v1_tops_2(X2,X1)
                    & v1_tops_2(X3,X1) )
                 => v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tops_2])).

cnf(c_0_18,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & v1_tops_2(esk4_0,esk3_0)
    & v1_tops_2(esk5_0,esk3_0)
    & ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1)
    | r2_hidden(esk1_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk1_3(X2,X3,X1),X2)
    | ~ r2_hidden(esk1_3(X2,X3,X1),X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk1_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk1_3(X1,X2,X2),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k1_zfmisc_1(u1_struct_0(esk3_0)) = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,k1_zfmisc_1(u1_struct_0(esk3_0))),esk5_0)
    | ~ r2_hidden(esk1_3(X1,X2,k1_zfmisc_1(u1_struct_0(esk3_0))),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = X3
    | r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,X3),X2)
    | r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,X3),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_tops_2(X28,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ r2_hidden(X29,X28)
        | v3_pre_topc(X29,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk2_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))
        | v1_tops_2(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))
        | ~ l1_pre_topc(X27) )
      & ( r2_hidden(esk2_2(X27,X28),X28)
        | v1_tops_2(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))
        | ~ l1_pre_topc(X27) )
      & ( ~ v3_pre_topc(esk2_2(X27,X28),X27)
        | v1_tops_2(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k2_xboole_0(X1,X2) = X2
    | ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(X2))
    | ~ r2_hidden(esk1_3(X1,X2,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0))) = k1_zfmisc_1(u1_struct_0(esk3_0))
    | r2_hidden(esk1_3(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0))),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_34])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

fof(c_0_51,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k4_subset_1(X22,X23,X24) = k2_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_52,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) = k1_zfmisc_1(u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_58,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( v1_tops_2(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_60,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk2_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_53]),c_0_54])])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_tops_2(k2_xboole_0(esk4_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_30]),c_0_35])])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_30]),c_0_59]),c_0_54])])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( v1_tops_2(X1,esk3_0)
    | ~ m1_subset_1(esk2_2(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | ~ r2_hidden(esk2_2(esk3_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_54])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_54])]),c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( v1_tops_2(X1,esk3_0)
    | ~ m1_subset_1(esk2_2(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    | ~ r2_hidden(esk2_2(esk3_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_65]),c_0_54])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k2_xboole_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_63]),c_0_54])]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_63])]),c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_63])]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_70]),c_0_71]),c_0_72]),
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
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.39/1.63  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.39/1.63  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.39/1.63  #
% 1.39/1.63  # Preprocessing time       : 0.016 s
% 1.39/1.63  # Presaturation interreduction done
% 1.39/1.63  
% 1.39/1.63  # Proof found!
% 1.39/1.63  # SZS status Theorem
% 1.39/1.63  # SZS output start CNFRefutation
% 1.39/1.63  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.39/1.63  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.39/1.63  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.39/1.63  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.39/1.63  fof(t20_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v1_tops_2(X2,X1)&v1_tops_2(X3,X1))=>v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tops_2)).
% 1.39/1.63  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.39/1.63  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.39/1.63  fof(d1_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v1_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 1.39/1.63  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 1.39/1.63  fof(c_0_9, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 1.39/1.63  fof(c_0_10, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 1.39/1.63  fof(c_0_11, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.39/1.63  cnf(c_0_12, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.39/1.63  fof(c_0_13, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 1.39/1.63  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.39/1.63  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.39/1.63  cnf(c_0_16, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.39/1.63  fof(c_0_17, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v1_tops_2(X2,X1)&v1_tops_2(X3,X1))=>v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t20_tops_2])).
% 1.39/1.63  cnf(c_0_18, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.39/1.63  cnf(c_0_19, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 1.39/1.63  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.39/1.63  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.39/1.63  cnf(c_0_22, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.39/1.63  cnf(c_0_23, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 1.39/1.63  fof(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))&((v1_tops_2(esk4_0,esk3_0)&v1_tops_2(esk5_0,esk3_0))&~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 1.39/1.63  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X3)|~r2_hidden(esk1_3(X3,X4,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.39/1.63  cnf(c_0_26, plain, (k2_xboole_0(X1,X2)=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.39/1.63  cnf(c_0_27, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.39/1.63  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)|r2_hidden(esk1_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_22])).
% 1.39/1.63  cnf(c_0_29, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 1.39/1.63  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.39/1.63  cnf(c_0_31, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.39/1.63  fof(c_0_32, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.39/1.63  cnf(c_0_33, plain, (X1=k2_xboole_0(X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(X1))|~r2_hidden(esk1_3(X2,X3,X1),X2)|~r2_hidden(esk1_3(X2,X3,X1),X4)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.39/1.63  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk1_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 1.39/1.63  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.39/1.63  cnf(c_0_36, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 1.39/1.63  cnf(c_0_37, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_31])).
% 1.39/1.63  cnf(c_0_38, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.39/1.63  fof(c_0_39, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.39/1.63  cnf(c_0_40, plain, (k2_xboole_0(X1,X2)=X2|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(esk1_3(X1,X2,X2),X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.39/1.63  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_35])).
% 1.39/1.63  cnf(c_0_42, negated_conjecture, (k1_zfmisc_1(u1_struct_0(esk3_0))=k2_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,k1_zfmisc_1(u1_struct_0(esk3_0))),esk5_0)|~r2_hidden(esk1_3(X1,X2,k1_zfmisc_1(u1_struct_0(esk3_0))),X1)), inference(spm,[status(thm)],[c_0_18, c_0_36])).
% 1.39/1.63  cnf(c_0_43, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=X3|r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,X3),X2)|r2_hidden(esk1_3(k2_xboole_0(X1,X2),X3,X3),X1)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 1.39/1.63  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.39/1.63  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_38])).
% 1.39/1.63  fof(c_0_46, plain, ![X27, X28, X29]:((~v1_tops_2(X28,X27)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27)))|(~r2_hidden(X29,X28)|v3_pre_topc(X29,X27)))|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))|~l1_pre_topc(X27))&((m1_subset_1(esk2_2(X27,X28),k1_zfmisc_1(u1_struct_0(X27)))|v1_tops_2(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))|~l1_pre_topc(X27))&((r2_hidden(esk2_2(X27,X28),X28)|v1_tops_2(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))|~l1_pre_topc(X27))&(~v3_pre_topc(esk2_2(X27,X28),X27)|v1_tops_2(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))|~l1_pre_topc(X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).
% 1.39/1.63  cnf(c_0_47, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.39/1.63  cnf(c_0_48, negated_conjecture, (k2_xboole_0(X1,X2)=X2|~m1_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(X2))|~r2_hidden(esk1_3(X1,X2,X2),esk4_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.39/1.63  cnf(c_0_49, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))=k1_zfmisc_1(u1_struct_0(esk3_0))|r2_hidden(esk1_3(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)),k1_zfmisc_1(u1_struct_0(esk3_0))),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_34])).
% 1.39/1.63  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 1.39/1.63  fof(c_0_51, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|~m1_subset_1(X24,k1_zfmisc_1(X22))|k4_subset_1(X22,X23,X24)=k2_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 1.39/1.63  cnf(c_0_52, plain, (v3_pre_topc(X3,X2)|~v1_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.39/1.63  cnf(c_0_53, negated_conjecture, (v1_tops_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.39/1.63  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.39/1.63  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_44, c_0_47])).
% 1.39/1.63  cnf(c_0_56, negated_conjecture, (k2_xboole_0(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))=k1_zfmisc_1(u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])]), c_0_20])).
% 1.39/1.63  cnf(c_0_57, negated_conjecture, (~v1_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.39/1.63  cnf(c_0_58, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.39/1.63  cnf(c_0_59, negated_conjecture, (v1_tops_2(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.39/1.63  cnf(c_0_60, plain, (v1_tops_2(X2,X1)|~v3_pre_topc(esk2_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.39/1.63  cnf(c_0_61, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_35]), c_0_53]), c_0_54])])).
% 1.39/1.63  cnf(c_0_62, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.39/1.63  cnf(c_0_63, negated_conjecture, (m1_subset_1(k2_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.39/1.63  cnf(c_0_64, negated_conjecture, (~v1_tops_2(k2_xboole_0(esk4_0,esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_30]), c_0_35])])).
% 1.39/1.63  cnf(c_0_65, negated_conjecture, (v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_30]), c_0_59]), c_0_54])])).
% 1.39/1.63  cnf(c_0_66, plain, (r2_hidden(esk2_2(X1,X2),X2)|v1_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.39/1.63  cnf(c_0_67, negated_conjecture, (v1_tops_2(X1,esk3_0)|~m1_subset_1(esk2_2(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))|~r2_hidden(esk2_2(esk3_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_54])])).
% 1.39/1.63  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_54])]), c_0_64])).
% 1.39/1.63  cnf(c_0_69, negated_conjecture, (v1_tops_2(X1,esk3_0)|~m1_subset_1(esk2_2(esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))|~r2_hidden(esk2_2(esk3_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_65]), c_0_54])])).
% 1.39/1.63  cnf(c_0_70, negated_conjecture, (r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),k2_xboole_0(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_63]), c_0_54])]), c_0_64])).
% 1.39/1.63  cnf(c_0_71, negated_conjecture, (~r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_63])]), c_0_64])).
% 1.39/1.63  cnf(c_0_72, negated_conjecture, (~r2_hidden(esk2_2(esk3_0,k2_xboole_0(esk4_0,esk5_0)),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_63])]), c_0_64])).
% 1.39/1.63  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_70]), c_0_71]), c_0_72]), ['proof']).
% 1.39/1.63  # SZS output end CNFRefutation
% 1.39/1.63  # Proof object total steps             : 74
% 1.39/1.63  # Proof object clause steps            : 55
% 1.39/1.63  # Proof object formula steps           : 19
% 1.39/1.63  # Proof object conjectures             : 26
% 1.39/1.63  # Proof object clause conjectures      : 23
% 1.39/1.63  # Proof object formula conjectures     : 3
% 1.39/1.63  # Proof object initial clauses used    : 23
% 1.39/1.63  # Proof object initial formulas used   : 9
% 1.39/1.63  # Proof object generating inferences   : 28
% 1.39/1.63  # Proof object simplifying inferences  : 36
% 1.39/1.63  # Training examples: 0 positive, 0 negative
% 1.39/1.63  # Parsed axioms                        : 9
% 1.39/1.63  # Removed by relevancy pruning/SinE    : 0
% 1.39/1.63  # Initial clauses                      : 25
% 1.39/1.63  # Removed in clause preprocessing      : 0
% 1.39/1.63  # Initial clauses in saturation        : 25
% 1.39/1.63  # Processed clauses                    : 19163
% 1.39/1.63  # ...of these trivial                  : 590
% 1.39/1.63  # ...subsumed                          : 16763
% 1.39/1.63  # ...remaining for further processing  : 1810
% 1.39/1.63  # Other redundant clauses eliminated   : 5
% 1.39/1.63  # Clauses deleted for lack of memory   : 0
% 1.39/1.63  # Backward-subsumed                    : 75
% 1.39/1.63  # Backward-rewritten                   : 0
% 1.39/1.63  # Generated clauses                    : 129788
% 1.39/1.63  # ...of the previous two non-trivial   : 118560
% 1.39/1.63  # Contextual simplify-reflections      : 51
% 1.39/1.63  # Paramodulations                      : 129163
% 1.39/1.63  # Factorizations                       : 620
% 1.39/1.63  # Equation resolutions                 : 5
% 1.39/1.63  # Propositional unsat checks           : 0
% 1.39/1.63  #    Propositional check models        : 0
% 1.39/1.63  #    Propositional check unsatisfiable : 0
% 1.39/1.63  #    Propositional clauses             : 0
% 1.39/1.63  #    Propositional clauses after purity: 0
% 1.39/1.63  #    Propositional unsat core size     : 0
% 1.39/1.63  #    Propositional preprocessing time  : 0.000
% 1.39/1.63  #    Propositional encoding time       : 0.000
% 1.39/1.63  #    Propositional solver time         : 0.000
% 1.39/1.63  #    Success case prop preproc time    : 0.000
% 1.39/1.63  #    Success case prop encoding time   : 0.000
% 1.39/1.63  #    Success case prop solver time     : 0.000
% 1.39/1.63  # Current number of processed clauses  : 1706
% 1.39/1.63  #    Positive orientable unit clauses  : 135
% 1.39/1.63  #    Positive unorientable unit clauses: 1
% 1.39/1.63  #    Negative unit clauses             : 6
% 1.39/1.63  #    Non-unit-clauses                  : 1564
% 1.39/1.63  # Current number of unprocessed clauses: 99355
% 1.39/1.63  # ...number of literals in the above   : 343272
% 1.39/1.63  # Current number of archived formulas  : 0
% 1.39/1.63  # Current number of archived clauses   : 99
% 1.39/1.63  # Clause-clause subsumption calls (NU) : 1115928
% 1.39/1.63  # Rec. Clause-clause subsumption calls : 832111
% 1.39/1.63  # Non-unit clause-clause subsumptions  : 16879
% 1.39/1.63  # Unit Clause-clause subsumption calls : 1633
% 1.39/1.63  # Rewrite failures with RHS unbound    : 0
% 1.39/1.63  # BW rewrite match attempts            : 1216
% 1.39/1.63  # BW rewrite match successes           : 6
% 1.39/1.63  # Condensation attempts                : 0
% 1.39/1.63  # Condensation successes               : 0
% 1.39/1.63  # Termbank termtop insertions          : 2284554
% 1.39/1.63  
% 1.39/1.63  # -------------------------------------------------
% 1.39/1.63  # User time                : 1.245 s
% 1.39/1.63  # System time              : 0.048 s
% 1.39/1.63  # Total time               : 1.294 s
% 1.39/1.63  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
