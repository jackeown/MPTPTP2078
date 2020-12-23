%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:08 EST 2020

% Result     : Theorem 0.40s
% Output     : CNFRefutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 350 expanded)
%              Number of clauses        :   45 ( 158 expanded)
%              Number of leaves         :    6 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 (1821 expanded)
%              Number of equality atoms :   19 ( 257 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t23_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( ( v2_tops_2(X2,X1)
                  & v2_tops_2(X3,X1) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tops_2)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( ( v2_tops_2(X2,X1)
                    & v2_tops_2(X3,X1) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tops_2])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X14,X13)
        | r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k2_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X18)
        | r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k2_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & v2_tops_2(esk5_0,esk4_0)
    & v2_tops_2(esk6_0,esk4_0)
    & ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( k2_xboole_0(esk6_0,X1) = X1
    | r2_hidden(esk2_3(esk6_0,X1,X1),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k2_xboole_0(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) = k1_zfmisc_1(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_34,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_tops_2(X26,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ r2_hidden(X27,X26)
        | v4_pre_topc(X27,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) )
      & ( m1_subset_1(esk3_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))
        | v2_tops_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) )
      & ( r2_hidden(esk3_2(X25,X26),X26)
        | v2_tops_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) )
      & ( ~ v4_pre_topc(esk3_2(X25,X26),X25)
        | v2_tops_2(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk4_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0))),X1)
    | r1_tarski(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_37,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
      | k4_subset_1(X20,X21,X22) = k2_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( v2_tops_2(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( v2_tops_2(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk3_2(X3,k2_xboole_0(X1,X2)),X2)
    | r2_hidden(esk3_2(X3,k2_xboole_0(X1,X2)),X1)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_tops_2(k2_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_15]),c_0_21])])).

cnf(c_0_49,negated_conjecture,
    ( v2_tops_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_15]),c_0_44]),c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0)
    | r2_hidden(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_45])]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_21]),c_0_49]),c_0_45])])).

cnf(c_0_53,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( v4_pre_topc(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0)
    | ~ m1_subset_1(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( ~ m1_subset_1(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_45]),c_0_47])]),c_0_48])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_45]),c_0_47])]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.40/0.60  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.40/0.60  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.40/0.60  #
% 0.40/0.60  # Preprocessing time       : 0.050 s
% 0.40/0.60  # Presaturation interreduction done
% 0.40/0.60  
% 0.40/0.60  # Proof found!
% 0.40/0.60  # SZS status Theorem
% 0.40/0.60  # SZS output start CNFRefutation
% 0.40/0.60  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.40/0.60  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.40/0.60  fof(t23_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v2_tops_2(X2,X1)&v2_tops_2(X3,X1))=>v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tops_2)).
% 0.40/0.60  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.40/0.60  fof(d2_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 0.40/0.60  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.40/0.60  fof(c_0_6, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.40/0.60  fof(c_0_7, plain, ![X23, X24]:((~m1_subset_1(X23,k1_zfmisc_1(X24))|r1_tarski(X23,X24))&(~r1_tarski(X23,X24)|m1_subset_1(X23,k1_zfmisc_1(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.40/0.60  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>((v2_tops_2(X2,X1)&v2_tops_2(X3,X1))=>v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)))))), inference(assume_negation,[status(cth)],[t23_tops_2])).
% 0.40/0.60  fof(c_0_9, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X14,X13)|(r2_hidden(X14,X11)|r2_hidden(X14,X12))|X13!=k2_xboole_0(X11,X12))&((~r2_hidden(X15,X11)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))&(~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k2_xboole_0(X11,X12))))&(((~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k2_xboole_0(X16,X17)))&(r2_hidden(esk2_3(X16,X17,X18),X18)|(r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k2_xboole_0(X16,X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.40/0.60  cnf(c_0_10, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.40/0.60  cnf(c_0_11, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.40/0.60  fof(c_0_12, negated_conjecture, (l1_pre_topc(esk4_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&((v2_tops_2(esk5_0,esk4_0)&v2_tops_2(esk6_0,esk4_0))&~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.40/0.60  cnf(c_0_13, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.40/0.60  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.40/0.60  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.40/0.60  cnf(c_0_16, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.40/0.60  cnf(c_0_17, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_13])).
% 0.40/0.60  cnf(c_0_18, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.40/0.60  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.40/0.60  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_17])).
% 0.40/0.60  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.40/0.60  cnf(c_0_22, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.40/0.60  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.40/0.60  cnf(c_0_24, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_18])).
% 0.40/0.60  cnf(c_0_25, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.40/0.60  cnf(c_0_26, negated_conjecture, (k2_xboole_0(esk6_0,X1)=X1|r2_hidden(esk2_3(esk6_0,X1,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.40/0.60  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_14, c_0_21])).
% 0.40/0.60  cnf(c_0_28, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_22])).
% 0.40/0.60  cnf(c_0_29, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.40/0.60  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.40/0.60  cnf(c_0_31, negated_conjecture, (k2_xboole_0(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))=k1_zfmisc_1(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_20])).
% 0.40/0.60  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk4_0))),esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_27])).
% 0.40/0.60  cnf(c_0_33, plain, (r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk1_2(k2_xboole_0(X1,X2),X3),X1)|r1_tarski(k2_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.40/0.60  fof(c_0_34, plain, ![X25, X26, X27]:((~v2_tops_2(X26,X25)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~r2_hidden(X27,X26)|v4_pre_topc(X27,X25)))|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|~l1_pre_topc(X25))&((m1_subset_1(esk3_2(X25,X26),k1_zfmisc_1(u1_struct_0(X25)))|v2_tops_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|~l1_pre_topc(X25))&((r2_hidden(esk3_2(X25,X26),X26)|v2_tops_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|~l1_pre_topc(X25))&(~v4_pre_topc(esk3_2(X25,X26),X25)|v2_tops_2(X26,X25)|~m1_subset_1(X26,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).
% 0.40/0.60  cnf(c_0_35, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(esk1_2(X1,k1_zfmisc_1(u1_struct_0(esk4_0))),esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.40/0.60  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_2(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0))),X1)|r1_tarski(k2_xboole_0(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.40/0.60  fof(c_0_37, plain, ![X20, X21, X22]:(~m1_subset_1(X21,k1_zfmisc_1(X20))|~m1_subset_1(X22,k1_zfmisc_1(X20))|k4_subset_1(X20,X21,X22)=k2_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.40/0.60  cnf(c_0_38, plain, (r2_hidden(esk3_2(X1,X2),X2)|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.40/0.60  cnf(c_0_39, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.40/0.60  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.40/0.60  cnf(c_0_41, negated_conjecture, (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(esk4_0)),esk5_0,esk6_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.40/0.60  cnf(c_0_42, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.40/0.60  cnf(c_0_43, plain, (v4_pre_topc(X3,X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.40/0.60  cnf(c_0_44, negated_conjecture, (v2_tops_2(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.40/0.60  cnf(c_0_45, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.40/0.60  cnf(c_0_46, plain, (v2_tops_2(k2_xboole_0(X1,X2),X3)|r2_hidden(esk3_2(X3,k2_xboole_0(X1,X2)),X2)|r2_hidden(esk3_2(X3,k2_xboole_0(X1,X2)),X1)|~l1_pre_topc(X3)|~m1_subset_1(k2_xboole_0(X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_28, c_0_38])).
% 0.40/0.60  cnf(c_0_47, negated_conjecture, (m1_subset_1(k2_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.40/0.60  cnf(c_0_48, negated_conjecture, (~v2_tops_2(k2_xboole_0(esk5_0,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_15]), c_0_21])])).
% 0.40/0.60  cnf(c_0_49, negated_conjecture, (v2_tops_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.40/0.60  cnf(c_0_50, negated_conjecture, (v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_15]), c_0_44]), c_0_45])])).
% 0.40/0.60  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk5_0)|r2_hidden(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_45])]), c_0_48])).
% 0.40/0.60  cnf(c_0_52, negated_conjecture, (v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_21]), c_0_49]), c_0_45])])).
% 0.40/0.60  cnf(c_0_53, plain, (v2_tops_2(X2,X1)|~v4_pre_topc(esk3_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.40/0.60  cnf(c_0_54, negated_conjecture, (v4_pre_topc(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),esk4_0)|~m1_subset_1(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.40/0.60  cnf(c_0_55, negated_conjecture, (~m1_subset_1(esk3_2(esk4_0,k2_xboole_0(esk5_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_45]), c_0_47])]), c_0_48])).
% 0.40/0.60  cnf(c_0_56, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.40/0.60  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_45]), c_0_47])]), c_0_48]), ['proof']).
% 0.40/0.60  # SZS output end CNFRefutation
% 0.40/0.60  # Proof object total steps             : 58
% 0.40/0.60  # Proof object clause steps            : 45
% 0.40/0.60  # Proof object formula steps           : 13
% 0.40/0.60  # Proof object conjectures             : 25
% 0.40/0.60  # Proof object clause conjectures      : 22
% 0.40/0.60  # Proof object formula conjectures     : 3
% 0.40/0.60  # Proof object initial clauses used    : 21
% 0.40/0.60  # Proof object initial formulas used   : 6
% 0.40/0.60  # Proof object generating inferences   : 24
% 0.40/0.60  # Proof object simplifying inferences  : 23
% 0.40/0.60  # Training examples: 0 positive, 0 negative
% 0.40/0.60  # Parsed axioms                        : 6
% 0.40/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.40/0.60  # Initial clauses                      : 22
% 0.40/0.60  # Removed in clause preprocessing      : 0
% 0.40/0.60  # Initial clauses in saturation        : 22
% 0.40/0.60  # Processed clauses                    : 1771
% 0.40/0.60  # ...of these trivial                  : 110
% 0.40/0.60  # ...subsumed                          : 1206
% 0.40/0.60  # ...remaining for further processing  : 455
% 0.40/0.60  # Other redundant clauses eliminated   : 3
% 0.40/0.60  # Clauses deleted for lack of memory   : 0
% 0.40/0.60  # Backward-subsumed                    : 3
% 0.40/0.60  # Backward-rewritten                   : 1
% 0.40/0.60  # Generated clauses                    : 12677
% 0.40/0.60  # ...of the previous two non-trivial   : 9961
% 0.40/0.60  # Contextual simplify-reflections      : 11
% 0.40/0.60  # Paramodulations                      : 12431
% 0.40/0.60  # Factorizations                       : 232
% 0.40/0.60  # Equation resolutions                 : 14
% 0.40/0.60  # Propositional unsat checks           : 0
% 0.40/0.60  #    Propositional check models        : 0
% 0.40/0.60  #    Propositional check unsatisfiable : 0
% 0.40/0.60  #    Propositional clauses             : 0
% 0.40/0.60  #    Propositional clauses after purity: 0
% 0.40/0.60  #    Propositional unsat core size     : 0
% 0.40/0.60  #    Propositional preprocessing time  : 0.000
% 0.40/0.60  #    Propositional encoding time       : 0.000
% 0.40/0.60  #    Propositional solver time         : 0.000
% 0.40/0.60  #    Success case prop preproc time    : 0.000
% 0.40/0.60  #    Success case prop encoding time   : 0.000
% 0.40/0.60  #    Success case prop solver time     : 0.000
% 0.40/0.60  # Current number of processed clauses  : 429
% 0.40/0.60  #    Positive orientable unit clauses  : 139
% 0.40/0.60  #    Positive unorientable unit clauses: 0
% 0.40/0.60  #    Negative unit clauses             : 4
% 0.40/0.60  #    Non-unit-clauses                  : 286
% 0.40/0.60  # Current number of unprocessed clauses: 8185
% 0.40/0.60  # ...number of literals in the above   : 26938
% 0.40/0.60  # Current number of archived formulas  : 0
% 0.40/0.60  # Current number of archived clauses   : 26
% 0.40/0.60  # Clause-clause subsumption calls (NU) : 19641
% 0.40/0.60  # Rec. Clause-clause subsumption calls : 14358
% 0.40/0.60  # Non-unit clause-clause subsumptions  : 1220
% 0.40/0.60  # Unit Clause-clause subsumption calls : 283
% 0.40/0.60  # Rewrite failures with RHS unbound    : 0
% 0.40/0.60  # BW rewrite match attempts            : 750
% 0.40/0.60  # BW rewrite match successes           : 1
% 0.40/0.60  # Condensation attempts                : 0
% 0.40/0.60  # Condensation successes               : 0
% 0.40/0.60  # Termbank termtop insertions          : 221374
% 0.40/0.60  
% 0.40/0.60  # -------------------------------------------------
% 0.40/0.60  # User time                : 0.250 s
% 0.40/0.60  # System time              : 0.014 s
% 0.40/0.60  # Total time               : 0.264 s
% 0.40/0.60  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
