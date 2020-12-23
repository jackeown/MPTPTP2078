%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:40 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   46 (2039 expanded)
%              Number of clauses        :   41 ( 702 expanded)
%              Number of leaves         :    2 ( 474 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 (20275 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   37 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_tops_1,conjecture,(
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
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ~ ( v3_pre_topc(X4,X1)
                        & r2_hidden(X3,X4)
                        & r1_xboole_0(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(c_0_2,negated_conjecture,(
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
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ~ ( v3_pre_topc(X4,X1)
                          & r2_hidden(X3,X4)
                          & r1_xboole_0(X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_tops_1])).

fof(c_0_3,plain,(
    ! [X5,X6,X7,X8] :
      ( ( ~ v2_struct_0(X5)
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v3_pre_topc(X8,X5)
        | ~ r2_hidden(X7,X8)
        | ~ r1_xboole_0(X6,X8)
        | ~ r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( v3_pre_topc(esk1_3(X5,X6,X7),X5)
        | v2_struct_0(X5)
        | r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(X7,esk1_3(X5,X6,X7))
        | v2_struct_0(X5)
        | r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( r1_xboole_0(X6,esk1_3(X5,X6,X7))
        | v2_struct_0(X5)
        | r2_hidden(X7,k2_pre_topc(X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).

fof(c_0_4,negated_conjecture,(
    ! [X14] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( v3_pre_topc(esk5_0,esk2_0)
        | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( r2_hidden(esk4_0,esk5_0)
        | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( r1_xboole_0(esk3_0,esk5_0)
        | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) )
      & ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | ~ v3_pre_topc(X14,esk2_0)
        | ~ r2_hidden(esk4_0,X14)
        | ~ r1_xboole_0(esk3_0,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).

cnf(c_0_5,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])]),c_0_8])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | v2_struct_0(X2)
    | r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,esk1_3(X2,X1,X3))
    | v2_struct_0(X2)
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_xboole_0(X4,X1)
    | ~ r2_hidden(X3,k2_pre_topc(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))
    | r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_6]),c_0_7])]),c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,esk3_0,X1),esk2_0)
    | r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_6]),c_0_7])]),c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_3(esk2_0,esk3_0,X1))
    | r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_6]),c_0_7])]),c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,X1)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X2,k2_pre_topc(esk2_0,esk3_0))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_6]),c_0_7])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0)
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk1_3(esk2_0,esk3_0,esk4_0))
    | r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_27,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r1_xboole_0(esk3_0,X1)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_10])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))
    | ~ r1_xboole_0(esk3_0,X1)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_23]),c_0_10])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))
    | r2_hidden(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0)
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0)
    | r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_38]),c_0_39])]),c_0_24]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_xboole_0(esk3_0,X1)
    | ~ v3_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_40]),c_0_10])])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_40])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_42]),c_0_43]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:10:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.12/0.37  # and selection function SelectComplexG.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t39_tops_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tops_1)).
% 0.12/0.37  fof(t54_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>(~(v2_struct_0(X1))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_pre_topc)).
% 0.12/0.37  fof(c_0_2, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k2_pre_topc(X1,X2))<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~(((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))&r1_xboole_0(X2,X4))))))))), inference(assume_negation,[status(cth)],[t39_tops_1])).
% 0.12/0.37  fof(c_0_3, plain, ![X5, X6, X7, X8]:(((~v2_struct_0(X5)|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X5)))|(~v3_pre_topc(X8,X5)|~r2_hidden(X7,X8)|~r1_xboole_0(X6,X8))|~r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5)))&((m1_subset_1(esk1_3(X5,X6,X7),k1_zfmisc_1(u1_struct_0(X5)))|v2_struct_0(X5)|r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(((v3_pre_topc(esk1_3(X5,X6,X7),X5)|v2_struct_0(X5)|r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))&(r2_hidden(X7,esk1_3(X5,X6,X7))|v2_struct_0(X5)|r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5)))&(r1_xboole_0(X6,esk1_3(X5,X6,X7))|v2_struct_0(X5)|r2_hidden(X7,k2_pre_topc(X5,X6))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|~l1_pre_topc(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_pre_topc])])])])])])).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ![X14]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(((m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)))&(((v3_pre_topc(esk5_0,esk2_0)|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)))&(r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))))&(r1_xboole_0(esk3_0,esk5_0)|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0)))))&(r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(esk2_0)))|(~v3_pre_topc(X14,esk2_0)|~r2_hidden(esk4_0,X14)|~r1_xboole_0(esk3_0,X14)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])])).
% 0.12/0.37  cnf(c_0_5, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_6, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_7, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_8, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5, c_0_6]), c_0_7])]), c_0_8])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_11, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|v2_struct_0(X2)|r2_hidden(X1,k2_pre_topc(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_12, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|v2_struct_0(X1)|r2_hidden(X3,k2_pre_topc(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_13, plain, (r1_xboole_0(X1,esk1_3(X2,X1,X3))|v2_struct_0(X2)|r2_hidden(X3,k2_pre_topc(X2,X1))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_14, plain, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,X2)|~r2_hidden(X3,X1)|~r1_xboole_0(X4,X1)|~r2_hidden(X3,k2_pre_topc(X2,X4))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk1_3(esk2_0,esk3_0,X1))|r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_6]), c_0_7])]), c_0_8])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (v3_pre_topc(esk1_3(esk2_0,esk3_0,X1),esk2_0)|r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_6]), c_0_7])]), c_0_8])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk3_0,esk1_3(esk2_0,esk3_0,X1))|r2_hidden(X1,k2_pre_topc(esk2_0,esk3_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_6]), c_0_7])]), c_0_8])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (~r1_xboole_0(esk3_0,X1)|~v3_pre_topc(X1,esk2_0)|~r2_hidden(X2,k2_pre_topc(esk2_0,esk3_0))|~r2_hidden(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_6]), c_0_7])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~v3_pre_topc(X1,esk2_0)|~r2_hidden(esk4_0,X1)|~r1_xboole_0(esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))|r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_17, c_0_10])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (v3_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk2_0)|r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_10])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (r1_xboole_0(esk3_0,esk1_3(esk2_0,esk3_0,esk4_0))|r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_10])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)|~r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))|~r1_xboole_0(esk3_0,X1)|~v3_pre_topc(X1,esk2_0)|~r2_hidden(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_10])])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_15])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,esk5_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_27, c_0_16])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_28, c_0_16])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))|~r1_xboole_0(esk3_0,X1)|~v3_pre_topc(X1,esk2_0)|~r2_hidden(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_23]), c_0_10])])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))|r2_hidden(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)|r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)|r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_35]), c_0_36]), c_0_37])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (r2_hidden(esk4_0,k2_pre_topc(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_38]), c_0_39])]), c_0_24]), c_0_25])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (~r1_xboole_0(esk3_0,X1)|~v3_pre_topc(X1,esk2_0)|~r2_hidden(esk4_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_40]), c_0_10])])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (r1_xboole_0(esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_40])])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_40])])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_40])])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_42]), c_0_43]), c_0_44])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 46
% 0.12/0.37  # Proof object clause steps            : 41
% 0.12/0.37  # Proof object formula steps           : 5
% 0.12/0.37  # Proof object conjectures             : 39
% 0.12/0.37  # Proof object clause conjectures      : 36
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 2
% 0.12/0.37  # Proof object generating inferences   : 24
% 0.12/0.37  # Proof object simplifying inferences  : 44
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 2
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 16
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 16
% 0.12/0.37  # Processed clauses                    : 80
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 4
% 0.12/0.37  # ...remaining for further processing  : 76
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 24
% 0.12/0.37  # Generated clauses                    : 64
% 0.12/0.37  # ...of the previous two non-trivial   : 63
% 0.12/0.37  # Contextual simplify-reflections      : 12
% 0.12/0.37  # Paramodulations                      : 64
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 35
% 0.12/0.37  #    Positive orientable unit clauses  : 11
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 23
% 0.12/0.37  # Current number of unprocessed clauses: 8
% 0.12/0.37  # ...number of literals in the above   : 30
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 41
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 359
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 218
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 12
% 0.12/0.37  # Unit Clause-clause subsumption calls : 76
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3357
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
