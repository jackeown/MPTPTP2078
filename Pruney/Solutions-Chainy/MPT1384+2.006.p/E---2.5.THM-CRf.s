%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:30 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  100 (1304 expanded)
%              Number of clauses        :   75 ( 530 expanded)
%              Number of leaves         :   12 ( 314 expanded)
%              Depth                    :   17
%              Number of atoms          :  336 (9005 expanded)
%              Number of equality atoms :    8 ( 127 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t9_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( m1_connsp_2(X4,X1,X3)
                            & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t48_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X2,X3)
               => r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t56_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X2,X1)
                  & r1_tarski(X2,X3) )
               => r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( m1_connsp_2(X4,X1,X3)
                              & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_connsp_2])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,negated_conjecture,(
    ! [X40,X41] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( r2_hidden(esk4_0,esk3_0)
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ m1_connsp_2(X40,esk2_0,esk4_0)
        | ~ r1_tarski(X40,esk3_0)
        | ~ v3_pre_topc(esk3_0,esk2_0) )
      & ( m1_subset_1(esk5_1(X41),k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r2_hidden(X41,esk3_0)
        | ~ m1_subset_1(X41,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( m1_connsp_2(esk5_1(X41),esk2_0,X41)
        | ~ r2_hidden(X41,esk3_0)
        | ~ m1_subset_1(X41,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) )
      & ( r1_tarski(esk5_1(X41),esk3_0)
        | ~ r2_hidden(X41,esk3_0)
        | ~ m1_subset_1(X41,u1_struct_0(esk2_0))
        | v3_pre_topc(esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | r1_tarski(k1_tops_1(X23,X24),X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_22])])).

fof(c_0_26,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
      | ~ r1_tarski(X26,X27)
      | r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).

fof(c_0_31,plain,(
    ! [X31,X32,X33] :
      ( ( ~ m1_connsp_2(X33,X31,X32)
        | r2_hidden(X32,k1_tops_1(X31,X33))
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ r2_hidden(X32,k1_tops_1(X31,X33))
        | m1_connsp_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_32,plain,(
    ! [X34,X35,X36] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | ~ m1_connsp_2(X36,X34,X35)
      | m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_36,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk5_1(X1),esk3_0)
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_29])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),k1_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_35]),c_0_22])])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_22])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( m1_connsp_2(esk5_1(X1),esk2_0,X1)
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | r1_tarski(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r1_tarski(X1,esk5_1(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_40]),c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | r1_tarski(esk5_1(X1),u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_42]),c_0_41])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_tops_1(X1,u1_struct_0(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,X2))
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | r2_hidden(X1,k1_tops_1(esk2_0,esk5_1(X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_22]),c_0_50])]),c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | r1_tarski(esk5_1(X1),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,u1_struct_0(esk2_0)),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_22])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_43]),c_0_16])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_55])).

fof(c_0_63,plain,(
    ! [X28,X29,X30] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ v3_pre_topc(X29,X28)
      | ~ r1_tarski(X29,X30)
      | r1_tarski(X29,k1_tops_1(X28,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).

cnf(c_0_64,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_41]),c_0_59])).

cnf(c_0_65,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_tops_1(esk2_0,u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_22])])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_69,plain,
    ( r1_tarski(X2,k1_tops_1(X1,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | r2_hidden(esk1_2(esk3_0,X1),k1_tops_1(esk2_0,esk3_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_47])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_45])).

fof(c_0_75,plain,(
    ! [X21,X22] :
      ( ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | v3_pre_topc(k1_tops_1(X21,X22),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_17]),c_0_22])])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0)
    | r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_47])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_62])])).

cnf(c_0_83,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0
    | ~ r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_25])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_17]),c_0_34])])).

cnf(c_0_86,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_connsp_2(X1,esk2_0,esk4_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_87,negated_conjecture,
    ( m1_connsp_2(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_22]),c_0_50])]),c_0_51])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_tarski(X1,k1_tops_1(esk2_0,X2))
    | ~ r1_tarski(X2,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_tops_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_82])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(k1_tops_1(esk2_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_22])])).

cnf(c_0_92,negated_conjecture,
    ( k1_tops_1(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(esk4_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))))
    | ~ r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_80])]),c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_17]),c_0_34])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_96,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_17])])).

cnf(c_0_97,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ r2_hidden(esk4_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_92]),c_0_92]),c_0_92]),c_0_92]),c_0_96]),c_0_98])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.14/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.028 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t9_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.14/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.40  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.14/0.40  fof(t44_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>r1_tarski(k1_tops_1(X1,X2),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 0.14/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.40  fof(t48_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X2,X3)=>r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 0.14/0.40  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.14/0.40  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.14/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.40  fof(t56_tops_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X2,X1)&r1_tarski(X2,X3))=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 0.14/0.40  fof(fc9_tops_1, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>v3_pre_topc(k1_tops_1(X1,X2),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 0.14/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2))))))))))), inference(assume_negation,[status(cth)],[t9_connsp_2])).
% 0.14/0.40  fof(c_0_13, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.40  fof(c_0_14, negated_conjecture, ![X40, X41]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((m1_subset_1(esk4_0,u1_struct_0(esk2_0))|~v3_pre_topc(esk3_0,esk2_0))&((r2_hidden(esk4_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0))&(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~m1_connsp_2(X40,esk2_0,esk4_0)|~r1_tarski(X40,esk3_0))|~v3_pre_topc(esk3_0,esk2_0))))&((m1_subset_1(esk5_1(X41),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X41,esk3_0)|~m1_subset_1(X41,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))&((m1_connsp_2(esk5_1(X41),esk2_0,X41)|~r2_hidden(X41,esk3_0)|~m1_subset_1(X41,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))&(r1_tarski(esk5_1(X41),esk3_0)|~r2_hidden(X41,esk3_0)|~m1_subset_1(X41,u1_struct_0(esk2_0))|v3_pre_topc(esk3_0,esk2_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.14/0.40  fof(c_0_15, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.14/0.40  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  fof(c_0_18, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|r1_tarski(k1_tops_1(X23,X24),X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).
% 0.14/0.40  cnf(c_0_19, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  cnf(c_0_20, negated_conjecture, (r1_tarski(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.40  cnf(c_0_21, plain, (r1_tarski(k1_tops_1(X1,X2),X2)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.40  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  fof(c_0_23, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.40  cnf(c_0_24, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.40  cnf(c_0_25, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_22])])).
% 0.14/0.40  fof(c_0_26, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.40  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  cnf(c_0_29, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.40  fof(c_0_30, plain, ![X25, X26, X27]:(~l1_pre_topc(X25)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|(~r1_tarski(X26,X27)|r1_tarski(k1_tops_1(X25,X26),k1_tops_1(X25,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_tops_1])])])).
% 0.14/0.40  fof(c_0_31, plain, ![X31, X32, X33]:((~m1_connsp_2(X33,X31,X32)|r2_hidden(X32,k1_tops_1(X31,X33))|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,u1_struct_0(X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~r2_hidden(X32,k1_tops_1(X31,X33))|m1_connsp_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))|~m1_subset_1(X32,u1_struct_0(X31))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.14/0.40  fof(c_0_32, plain, ![X34, X35, X36]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|~m1_subset_1(X35,u1_struct_0(X34))|(~m1_connsp_2(X36,X34,X35)|m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.14/0.40  cnf(c_0_33, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.40  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.14/0.40  cnf(c_0_35, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.14/0.40  fof(c_0_36, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.40  cnf(c_0_37, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.40  cnf(c_0_38, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  cnf(c_0_39, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.40  cnf(c_0_40, negated_conjecture, (r1_tarski(esk5_1(X1),esk3_0)|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_41, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_17])).
% 0.14/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.14/0.40  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_29])).
% 0.14/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),k1_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_35]), c_0_22])])).
% 0.14/0.40  cnf(c_0_46, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),k1_tops_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_17]), c_0_22])])).
% 0.14/0.40  cnf(c_0_48, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.40  cnf(c_0_49, negated_conjecture, (m1_connsp_2(esk5_1(X1),esk2_0,X1)|v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_52, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|r1_tarski(X1,esk3_0)|~r2_hidden(X2,esk3_0)|~r1_tarski(X1,esk5_1(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_40]), c_0_41])).
% 0.14/0.40  cnf(c_0_53, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|r1_tarski(esk5_1(X1),u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_42]), c_0_41])).
% 0.14/0.40  cnf(c_0_54, plain, (r1_tarski(k1_tops_1(X1,u1_struct_0(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_21, c_0_43])).
% 0.14/0.40  cnf(c_0_55, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.40  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,k1_tops_1(esk2_0,X2))|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.40  cnf(c_0_57, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|r2_hidden(X1,k1_tops_1(esk2_0,esk5_1(X1)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_22]), c_0_50])]), c_0_51])).
% 0.14/0.40  cnf(c_0_58, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|r1_tarski(esk5_1(X1),esk3_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_34])).
% 0.14/0.40  cnf(c_0_59, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|m1_subset_1(esk5_1(X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_53])).
% 0.14/0.40  cnf(c_0_60, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,u1_struct_0(esk2_0)),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_54, c_0_22])).
% 0.14/0.40  cnf(c_0_61, plain, (r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_43]), c_0_16])).
% 0.14/0.40  cnf(c_0_62, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_28, c_0_55])).
% 0.14/0.40  fof(c_0_63, plain, ![X28, X29, X30]:(~l1_pre_topc(X28)|(~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X28)))|(~v3_pre_topc(X29,X28)|~r1_tarski(X29,X30)|r1_tarski(X29,k1_tops_1(X28,X30)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_tops_1])])])).
% 0.14/0.40  cnf(c_0_64, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|r2_hidden(X1,k1_tops_1(esk2_0,esk3_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_41]), c_0_59])).
% 0.14/0.40  cnf(c_0_65, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_66, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r1_tarski(X1,k1_tops_1(esk2_0,u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_19, c_0_60])).
% 0.14/0.40  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_tops_1(esk2_0,u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_22])])).
% 0.14/0.40  cnf(c_0_68, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 0.14/0.40  cnf(c_0_69, plain, (r1_tarski(X2,k1_tops_1(X1,X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_pre_topc(X2,X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.14/0.40  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_71, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|r2_hidden(esk1_2(esk3_0,X1),k1_tops_1(esk2_0,esk3_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.14/0.40  cnf(c_0_72, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.14/0.40  cnf(c_0_73, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,X1),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_47])).
% 0.14/0.40  cnf(c_0_74, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_45])).
% 0.14/0.40  fof(c_0_75, plain, ![X21, X22]:(~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|v3_pre_topc(k1_tops_1(X21,X22),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).
% 0.14/0.40  cnf(c_0_76, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.40  cnf(c_0_77, negated_conjecture, (r1_tarski(X1,k1_tops_1(esk2_0,esk3_0))|~v3_pre_topc(X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_17]), c_0_22])])).
% 0.14/0.40  cnf(c_0_78, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)|r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.14/0.40  cnf(c_0_79, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.40  cnf(c_0_80, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_28, c_0_72])).
% 0.14/0.40  cnf(c_0_81, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,X1),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_68, c_0_47])).
% 0.14/0.40  cnf(c_0_82, negated_conjecture, (m1_subset_1(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_zfmisc_1(k1_tops_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_62])])).
% 0.14/0.40  cnf(c_0_83, plain, (v3_pre_topc(k1_tops_1(X1,X2),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.14/0.40  cnf(c_0_84, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0|~r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_25])).
% 0.14/0.40  cnf(c_0_85, negated_conjecture, (r1_tarski(esk3_0,k1_tops_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_17]), c_0_34])])).
% 0.14/0.40  cnf(c_0_86, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_connsp_2(X1,esk2_0,esk4_0)|~r1_tarski(X1,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_87, negated_conjecture, (m1_connsp_2(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_22]), c_0_50])]), c_0_51])).
% 0.14/0.40  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_89, negated_conjecture, (r1_tarski(X1,esk3_0)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_tarski(X1,k1_tops_1(esk2_0,X2))|~r1_tarski(X2,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_81])).
% 0.14/0.40  cnf(c_0_90, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),k1_tops_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_16, c_0_82])).
% 0.14/0.40  cnf(c_0_91, negated_conjecture, (v3_pre_topc(k1_tops_1(esk2_0,X1),esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_22])])).
% 0.14/0.40  cnf(c_0_92, negated_conjecture, (k1_tops_1(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 0.14/0.40  cnf(c_0_93, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(esk4_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))))|~r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_80])]), c_0_88])).
% 0.14/0.40  cnf(c_0_94, negated_conjecture, (r1_tarski(k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_17]), c_0_34])])).
% 0.14/0.40  cnf(c_0_95, negated_conjecture, (r2_hidden(esk4_0,esk3_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_96, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_17])])).
% 0.14/0.40  cnf(c_0_97, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~r2_hidden(esk4_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,k1_tops_1(esk2_0,esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])])).
% 0.14/0.40  cnf(c_0_98, negated_conjecture, (r2_hidden(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])])).
% 0.14/0.40  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_92]), c_0_92]), c_0_92]), c_0_92]), c_0_96]), c_0_98])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 100
% 0.14/0.40  # Proof object clause steps            : 75
% 0.14/0.40  # Proof object formula steps           : 25
% 0.14/0.40  # Proof object conjectures             : 57
% 0.14/0.40  # Proof object clause conjectures      : 54
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 26
% 0.14/0.40  # Proof object initial formulas used   : 12
% 0.14/0.40  # Proof object generating inferences   : 43
% 0.14/0.40  # Proof object simplifying inferences  : 54
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 12
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 27
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 27
% 0.14/0.40  # Processed clauses                    : 296
% 0.14/0.40  # ...of these trivial                  : 10
% 0.14/0.40  # ...subsumed                          : 45
% 0.14/0.40  # ...remaining for further processing  : 240
% 0.14/0.40  # Other redundant clauses eliminated   : 2
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 4
% 0.14/0.40  # Backward-rewritten                   : 124
% 0.14/0.40  # Generated clauses                    : 565
% 0.14/0.40  # ...of the previous two non-trivial   : 523
% 0.14/0.40  # Contextual simplify-reflections      : 22
% 0.14/0.40  # Paramodulations                      : 563
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 2
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 84
% 0.14/0.40  #    Positive orientable unit clauses  : 18
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 1
% 0.14/0.40  #    Non-unit-clauses                  : 65
% 0.14/0.40  # Current number of unprocessed clauses: 272
% 0.14/0.40  # ...number of literals in the above   : 806
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 154
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 2858
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 1533
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 71
% 0.14/0.40  # Unit Clause-clause subsumption calls : 70
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 43
% 0.14/0.40  # BW rewrite match successes           : 4
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 14841
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.053 s
% 0.14/0.40  # System time              : 0.005 s
% 0.14/0.40  # Total time               : 0.058 s
% 0.14/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
