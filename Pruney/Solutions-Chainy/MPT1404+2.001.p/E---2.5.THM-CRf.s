%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 (2385 expanded)
%              Number of clauses        :   66 ( 857 expanded)
%              Number of leaves         :    7 ( 557 expanded)
%              Depth                    :   20
%              Number of atoms          :  364 (18388 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_connsp_2(X4,X1,X3)
                   => ~ r1_xboole_0(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_connsp_2)).

fof(t54_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ( ~ v2_struct_0(X1)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ~ ( v3_pre_topc(X4,X1)
                          & r2_hidden(X3,X4)
                          & r1_xboole_0(X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_pre_topc)).

fof(t8_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X3)
                    & r2_hidden(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

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

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_pre_topc(X1,X2))
                <=> ! [X4] :
                      ( m1_connsp_2(X4,X1,X3)
                     => ~ r1_xboole_0(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_connsp_2])).

fof(c_0_8,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ v2_struct_0(X10)
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ v3_pre_topc(X13,X10)
        | ~ r2_hidden(X12,X13)
        | ~ r1_xboole_0(X11,X13)
        | ~ r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X10)))
        | v2_struct_0(X10)
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( v3_pre_topc(esk1_3(X10,X11,X12),X10)
        | v2_struct_0(X10)
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(X12,esk1_3(X10,X11,X12))
        | v2_struct_0(X10)
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( r1_xboole_0(X11,esk1_3(X10,X11,X12))
        | v2_struct_0(X10)
        | r2_hidden(X12,k2_pre_topc(X10,X11))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X30] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & ( m1_connsp_2(esk6_0,esk3_0,esk5_0)
        | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( r1_xboole_0(esk6_0,esk4_0)
        | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) )
      & ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
        | ~ m1_connsp_2(X30,esk3_0,esk5_0)
        | ~ r1_xboole_0(X30,esk4_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

fof(c_0_10,plain,(
    ! [X21,X22,X23,X25] :
      ( ( m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_connsp_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_pre_topc(esk2_3(X21,X22,X23),X21)
        | ~ m1_connsp_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(esk2_3(X21,X22,X23),X23)
        | ~ m1_connsp_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(X22,esk2_3(X21,X22,X23))
        | ~ m1_connsp_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v3_pre_topc(X25,X21)
        | ~ r1_tarski(X25,X23)
        | ~ r2_hidden(X22,X25)
        | m1_connsp_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m1_subset_1(X22,u1_struct_0(X21))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_connsp_2(X17,X15,X16)
      | m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | r1_tarski(esk2_3(X1,X2,X3),X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk3_0,esk5_0)
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_3(esk3_0,esk5_0,X1),X1)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk3_0,esk5_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r1_tarski(esk2_3(esk3_0,esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0)
    | ~ r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X4,X1)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_27,c_0_17])).

fof(c_0_35,plain,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),X1)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r1_xboole_0(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,esk2_3(X1,X2,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_39,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_13]),c_0_14])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk5_0,esk2_3(esk3_0,esk5_0,X1))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_19]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk3_0,esk5_0,X1),esk3_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_19]),c_0_21]),c_0_14])]),c_0_15])).

fof(c_0_46,plain,(
    ! [X18,X19,X20] :
      ( v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ v3_pre_topc(X19,X18)
      | ~ r2_hidden(X20,X19)
      | m1_connsp_2(X19,X18,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_19])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | r1_xboole_0(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_51,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk3_0,esk5_0,esk6_0),esk3_0)
    | m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_26])).

cnf(c_0_52,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk3_0,esk4_0,X1),esk3_0)
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | v2_struct_0(X2)
    | r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_57,plain,
    ( r1_xboole_0(X1,esk1_3(X2,X1,X3))
    | v2_struct_0(X2)
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_58,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,X1)
    | ~ v3_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0)
    | ~ r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_21]),c_0_14])]),c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk3_0,esk4_0,X1))
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | r1_xboole_0(esk4_0,esk1_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,X1)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | r1_xboole_0(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_66,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0)
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_19])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | r1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_68])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_3(esk3_0,esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_68]),c_0_19])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk5_0,esk2_3(esk3_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),X1)
    | ~ r1_xboole_0(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_68])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v3_pre_topc(esk2_3(esk3_0,esk5_0,esk6_0),esk3_0)
    | ~ r1_xboole_0(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk3_0,esk5_0,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_78]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:40:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EA
% 0.20/0.39  # and selection function SelectLComplex.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.027 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t34_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_connsp_2(X4,X1,X3)=>~(r1_xboole_0(X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_connsp_2)).
% 0.20/0.39  fof(t54_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>(~(v2_struct_0(X1))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_pre_topc)).
% 0.20/0.39  fof(t8_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>?[X4]:(((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v3_pre_topc(X4,X1))&r1_tarski(X4,X3))&r2_hidden(X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 0.20/0.39  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.20/0.39  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.39  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.39  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.20/0.39  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_connsp_2(X4,X1,X3)=>~(r1_xboole_0(X4,X2)))))))), inference(assume_negation,[status(cth)],[t34_connsp_2])).
% 0.20/0.39  fof(c_0_8, plain, ![X10, X11, X12, X13]:(((~v2_struct_0(X10)|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~v3_pre_topc(X13,X10)|~r2_hidden(X12,X13)|~r1_xboole_0(X11,X13))|~r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10)))&((m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X10)))|v2_struct_0(X10)|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(((v3_pre_topc(esk1_3(X10,X11,X12),X10)|v2_struct_0(X10)|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(r2_hidden(X12,esk1_3(X10,X11,X12))|v2_struct_0(X10)|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10)))&(r1_xboole_0(X11,esk1_3(X10,X11,X12))|v2_struct_0(X10)|r2_hidden(X12,k2_pre_topc(X10,X11))|~m1_subset_1(X12,u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ![X30]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(((m1_connsp_2(esk6_0,esk3_0,esk5_0)|~r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)))&(r1_xboole_0(esk6_0,esk4_0)|~r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))))&(r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))|(~m1_connsp_2(X30,esk3_0,esk5_0)|~r1_xboole_0(X30,esk4_0))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).
% 0.20/0.39  fof(c_0_10, plain, ![X21, X22, X23, X25]:(((((m1_subset_1(esk2_3(X21,X22,X23),k1_zfmisc_1(u1_struct_0(X21)))|~m1_connsp_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v3_pre_topc(esk2_3(X21,X22,X23),X21)|~m1_connsp_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r1_tarski(esk2_3(X21,X22,X23),X23)|~m1_connsp_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r2_hidden(X22,esk2_3(X21,X22,X23))|~m1_connsp_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X21)))|~v3_pre_topc(X25,X21)|~r1_tarski(X25,X23)|~r2_hidden(X22,X25)|m1_connsp_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m1_subset_1(X22,u1_struct_0(X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).
% 0.20/0.39  fof(c_0_11, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|~m1_subset_1(X16,u1_struct_0(X15))|(~m1_connsp_2(X17,X15,X16)|m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.20/0.39  cnf(c_0_12, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_16, plain, (r1_tarski(esk2_3(X1,X2,X3),X3)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_17, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_20, plain, (v2_struct_0(X1)|r1_tarski(esk2_3(X1,X2,X3),X3)|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (m1_connsp_2(esk6_0,esk3_0,esk5_0)|~r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  fof(c_0_24, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_xboole_0(X8,X9)|r1_xboole_0(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (r1_tarski(esk2_3(esk3_0,esk5_0,X1),X1)|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_19]), c_0_21]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (m1_connsp_2(esk6_0,esk3_0,esk5_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.39  cnf(c_0_27, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_28, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|r1_tarski(esk2_3(esk3_0,esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)|~r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_31, plain, (r2_hidden(X1,esk2_3(X2,X1,X3))|v2_struct_0(X2)|~m1_connsp_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_32, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_33, plain, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X4,X1)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_34, plain, (v2_struct_0(X1)|m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_27, c_0_17])).
% 0.20/0.39  fof(c_0_35, plain, ![X5, X6]:(~r1_xboole_0(X5,X6)|r1_xboole_0(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),X1)|~r1_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|r1_xboole_0(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_23])).
% 0.20/0.39  cnf(c_0_38, plain, (v2_struct_0(X1)|r2_hidden(X2,esk2_3(X1,X2,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_31, c_0_17])).
% 0.20/0.39  cnf(c_0_39, plain, (v3_pre_topc(esk2_3(X1,X2,X3),X1)|v2_struct_0(X1)|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_32, c_0_17])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (~v3_pre_topc(X1,esk3_0)|~r2_hidden(X2,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(X2,u1_struct_0(esk3_0))|~r1_xboole_0(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_13]), c_0_14])])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_21]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_42, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (r2_hidden(esk5_0,esk2_3(esk3_0,esk5_0,X1))|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_19]), c_0_21]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (v3_pre_topc(esk2_3(esk3_0,esk5_0,X1),esk3_0)|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_19]), c_0_21]), c_0_14])]), c_0_15])).
% 0.20/0.39  fof(c_0_46, plain, ![X18, X19, X20]:(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(~m1_subset_1(X20,u1_struct_0(X18))|(~v3_pre_topc(X19,X18)|~r2_hidden(X20,X19)|m1_connsp_2(X19,X18,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X1,esk3_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_xboole_0(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_19])])).
% 0.20/0.39  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_26])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|r1_xboole_0(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (v3_pre_topc(esk2_3(esk3_0,esk5_0,esk6_0),esk3_0)|m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_45, c_0_26])).
% 0.20/0.39  cnf(c_0_52, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|v2_struct_0(X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_53, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (v3_pre_topc(esk1_3(esk3_0,esk4_0,X1),esk3_0)|r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_56, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|v2_struct_0(X2)|r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_57, plain, (r1_xboole_0(X1,esk1_3(X2,X1,X3))|v2_struct_0(X2)|r2_hidden(X3,k2_pre_topc(X2,X1))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (m1_connsp_2(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,X1)|~v3_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0)|~r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_21]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (v3_pre_topc(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0)|r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_55, c_0_19])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,esk1_3(esk3_0,esk4_0,X1))|r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))|r1_xboole_0(esk4_0,esk1_3(esk3_0,esk4_0,X1))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (m1_connsp_2(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,X1)|r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))|~r2_hidden(X1,esk1_3(esk3_0,esk4_0,esk5_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (r2_hidden(esk5_0,esk1_3(esk3_0,esk4_0,esk5_0))|r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_19])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))|r1_xboole_0(esk4_0,esk1_3(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_61, c_0_19])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))|~m1_connsp_2(X1,esk3_0,esk5_0)|~r1_xboole_0(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (m1_connsp_2(esk1_3(esk3_0,esk4_0,esk5_0),esk3_0,esk5_0)|r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_19])])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))|r1_xboole_0(esk1_3(esk3_0,esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_64])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (m1_connsp_2(esk6_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_68])])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_3(esk3_0,esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_69])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (~v3_pre_topc(X1,esk3_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_xboole_0(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_68]), c_0_19])])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_41, c_0_69])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (r2_hidden(esk5_0,esk2_3(esk3_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_44, c_0_69])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),X1)|~r1_xboole_0(esk6_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_70])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (r1_xboole_0(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_68])])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (~v3_pre_topc(esk2_3(esk3_0,esk5_0,esk6_0),esk3_0)|~r1_xboole_0(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (v3_pre_topc(esk2_3(esk3_0,esk5_0,esk6_0),esk3_0)), inference(spm,[status(thm)],[c_0_45, c_0_69])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk2_3(esk3_0,esk5_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (~r1_xboole_0(esk4_0,esk2_3(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_78]), c_0_79]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 81
% 0.20/0.39  # Proof object clause steps            : 66
% 0.20/0.39  # Proof object formula steps           : 15
% 0.20/0.39  # Proof object conjectures             : 52
% 0.20/0.39  # Proof object clause conjectures      : 49
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 21
% 0.20/0.39  # Proof object initial formulas used   : 7
% 0.20/0.39  # Proof object generating inferences   : 38
% 0.20/0.39  # Proof object simplifying inferences  : 57
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 7
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 23
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 23
% 0.20/0.39  # Processed clauses                    : 111
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 11
% 0.20/0.39  # ...remaining for further processing  : 100
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 1
% 0.20/0.39  # Backward-rewritten                   : 23
% 0.20/0.39  # Generated clauses                    : 106
% 0.20/0.39  # ...of the previous two non-trivial   : 106
% 0.20/0.39  # Contextual simplify-reflections      : 8
% 0.20/0.39  # Paramodulations                      : 106
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 53
% 0.20/0.39  #    Positive orientable unit clauses  : 15
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 36
% 0.20/0.39  # Current number of unprocessed clauses: 26
% 0.20/0.39  # ...number of literals in the above   : 96
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 47
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 350
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 146
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.39  # Unit Clause-clause subsumption calls : 51
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 7
% 0.20/0.39  # BW rewrite match successes           : 3
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5697
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.033 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.038 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
