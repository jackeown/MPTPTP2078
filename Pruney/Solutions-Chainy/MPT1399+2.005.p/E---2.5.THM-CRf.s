%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 113 expanded)
%              Number of clauses        :   33 (  42 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  282 ( 897 expanded)
%              Number of equality atoms :   10 (  52 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r2_hidden(X4,X3)
                      <=> ( v3_pre_topc(X4,X1)
                          & v4_pre_topc(X4,X1)
                          & r2_hidden(X2,X4) ) ) )
                  & X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r2_hidden(X4,X3)
                        <=> ( v3_pre_topc(X4,X1)
                            & v4_pre_topc(X4,X1)
                            & r2_hidden(X2,X4) ) ) )
                    & X3 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_connsp_2])).

fof(c_0_14,negated_conjecture,(
    ! [X31] :
      ( ~ v2_struct_0(esk5_0)
      & v2_pre_topc(esk5_0)
      & l1_pre_topc(esk5_0)
      & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
      & ( v3_pre_topc(X31,esk5_0)
        | ~ r2_hidden(X31,esk7_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & ( v4_pre_topc(X31,esk5_0)
        | ~ r2_hidden(X31,esk7_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & ( r2_hidden(esk6_0,X31)
        | ~ r2_hidden(X31,esk7_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & ( ~ v3_pre_topc(X31,esk5_0)
        | ~ v4_pre_topc(X31,esk5_0)
        | ~ r2_hidden(esk6_0,X31)
        | r2_hidden(X31,esk7_0)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0))) )
      & esk7_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | ~ r1_tarski(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_16,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ( ~ v3_pre_topc(X23,X22)
        | r2_hidden(X23,u1_pre_topc(X22))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) )
      & ( ~ r2_hidden(X23,u1_pre_topc(X22))
        | v3_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk5_0)
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_27,plain,(
    ! [X25] :
      ( ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v4_pre_topc(k2_struct_0(X25),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

fof(c_0_28,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_29,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_30,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk5_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_31,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_33,plain,(
    ! [X21] :
      ( ~ l1_struct_0(X21)
      | k2_struct_0(X21) = u1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(k2_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(esk6_0,k2_struct_0(esk5_0))
    | ~ m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_26])])).

cnf(c_0_37,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_40,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,X11)
      | v1_xboole_0(X11)
      | r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_41,negated_conjecture,
    ( ~ l1_struct_0(esk5_0)
    | ~ r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_43,plain,(
    ! [X14,X15,X16,X17] :
      ( ( r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r1_tarski(X15,u1_pre_topc(X14))
        | r2_hidden(k5_setfam_1(u1_struct_0(X14),X15),u1_pre_topc(X14))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X16,u1_pre_topc(X14))
        | ~ r2_hidden(X17,u1_pre_topc(X14))
        | r2_hidden(k9_subset_1(u1_struct_0(X14),X16,X17),u1_pre_topc(X14))
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk2_1(X14),u1_pre_topc(X14))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_1(X14),u1_pre_topc(X14))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))
        | m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk2_1(X14),u1_pre_topc(X14))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_1(X14),u1_pre_topc(X14))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))
        | r1_tarski(esk1_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk2_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_1(X14),u1_pre_topc(X14))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))
        | ~ r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))
        | v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_44,plain,(
    ! [X26] :
      ( ( m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( ~ v1_xboole_0(esk4_1(X26))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v4_pre_topc(esk4_1(X26),X26)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26])])).

cnf(c_0_48,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_xboole_0(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_32]),c_0_26])])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_32]),c_0_26])]),c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk4_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk4_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_32]),c_0_26])]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:47:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.028 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.20/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.37  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.20/0.37  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.20/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.37  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.37  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.37  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.20/0.37  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.37  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.20/0.37  fof(c_0_14, negated_conjecture, ![X31]:(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))&(((((v3_pre_topc(X31,esk5_0)|~r2_hidden(X31,esk7_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0))))&(v4_pre_topc(X31,esk5_0)|~r2_hidden(X31,esk7_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0)))))&(r2_hidden(esk6_0,X31)|~r2_hidden(X31,esk7_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0)))))&(~v3_pre_topc(X31,esk5_0)|~v4_pre_topc(X31,esk5_0)|~r2_hidden(esk6_0,X31)|r2_hidden(X31,esk7_0)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk5_0)))))&esk7_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])])).
% 0.20/0.37  fof(c_0_15, plain, ![X12, X13]:(~r2_hidden(X12,X13)|~r1_tarski(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.37  fof(c_0_16, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk7_0)|~v3_pre_topc(X1,esk5_0)|~v4_pre_topc(X1,esk5_0)|~r2_hidden(esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (esk7_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_20, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v4_pre_topc(X1,esk5_0)|~v3_pre_topc(X1,esk5_0)|~r2_hidden(esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.37  cnf(c_0_22, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.37  fof(c_0_23, plain, ![X22, X23]:((~v3_pre_topc(X23,X22)|r2_hidden(X23,u1_pre_topc(X22))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))&(~r2_hidden(X23,u1_pre_topc(X22))|v3_pre_topc(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|~l1_pre_topc(X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (~v4_pre_topc(X1,esk5_0)|~v3_pre_topc(X1,esk5_0)|~r2_hidden(esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  cnf(c_0_25, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  fof(c_0_27, plain, ![X25]:(~v2_pre_topc(X25)|~l1_pre_topc(X25)|v4_pre_topc(k2_struct_0(X25),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.20/0.37  fof(c_0_28, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.37  fof(c_0_29, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (~v4_pre_topc(X1,esk5_0)|~r2_hidden(X1,u1_pre_topc(esk5_0))|~r2_hidden(esk6_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.37  cnf(c_0_31, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  fof(c_0_33, plain, ![X21]:(~l1_struct_0(X21)|k2_struct_0(X21)=u1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.37  cnf(c_0_34, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.37  cnf(c_0_35, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (~r2_hidden(k2_struct_0(esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(esk6_0,k2_struct_0(esk5_0))|~m1_subset_1(k2_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_26])])).
% 0.20/0.37  cnf(c_0_37, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.37  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.37  fof(c_0_39, plain, ![X24]:(~l1_pre_topc(X24)|l1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.37  fof(c_0_40, plain, ![X10, X11]:(~m1_subset_1(X10,X11)|(v1_xboole_0(X11)|r2_hidden(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (~l1_struct_0(esk5_0)|~r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.37  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  fof(c_0_43, plain, ![X14, X15, X16, X17]:((((r2_hidden(u1_struct_0(X14),u1_pre_topc(X14))|~v2_pre_topc(X14)|~l1_pre_topc(X14))&(~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|(~r1_tarski(X15,u1_pre_topc(X14))|r2_hidden(k5_setfam_1(u1_struct_0(X14),X15),u1_pre_topc(X14)))|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X14)))|(~r2_hidden(X16,u1_pre_topc(X14))|~r2_hidden(X17,u1_pre_topc(X14))|r2_hidden(k9_subset_1(u1_struct_0(X14),X16,X17),u1_pre_topc(X14))))|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(((m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&((m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(((r2_hidden(esk2_1(X14),u1_pre_topc(X14))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(r2_hidden(esk3_1(X14),u1_pre_topc(X14))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))|(m1_subset_1(esk1_1(X14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X14))))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))))&(((m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&((m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(((r2_hidden(esk2_1(X14),u1_pre_topc(X14))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(r2_hidden(esk3_1(X14),u1_pre_topc(X14))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))|(r1_tarski(esk1_1(X14),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))))&((m1_subset_1(esk2_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&((m1_subset_1(esk3_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(((r2_hidden(esk2_1(X14),u1_pre_topc(X14))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14))&(r2_hidden(esk3_1(X14),u1_pre_topc(X14))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~r2_hidden(k9_subset_1(u1_struct_0(X14),esk2_1(X14),esk3_1(X14)),u1_pre_topc(X14))|(~r2_hidden(k5_setfam_1(u1_struct_0(X14),esk1_1(X14)),u1_pre_topc(X14))|~r2_hidden(u1_struct_0(X14),u1_pre_topc(X14)))|v2_pre_topc(X14)|~l1_pre_topc(X14)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.37  fof(c_0_44, plain, ![X26]:(((m1_subset_1(esk4_1(X26),k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(~v1_xboole_0(esk4_1(X26))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))))&(v4_pre_topc(esk4_1(X26),X26)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.20/0.37  cnf(c_0_45, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.37  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (~r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))|~r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_26])])).
% 0.20/0.37  cnf(c_0_48, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.37  fof(c_0_49, plain, ![X8, X9]:(~v1_xboole_0(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.37  cnf(c_0_50, plain, (m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.37  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_52, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.37  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_32]), c_0_26])])).
% 0.20/0.37  cnf(c_0_54, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.37  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk4_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_32]), c_0_26])]), c_0_51])).
% 0.20/0.37  cnf(c_0_56, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.37  cnf(c_0_57, plain, (v2_struct_0(X1)|~v1_xboole_0(esk4_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.37  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk4_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.20/0.37  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_32]), c_0_26])]), c_0_51]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 60
% 0.20/0.37  # Proof object clause steps            : 33
% 0.20/0.37  # Proof object formula steps           : 27
% 0.20/0.37  # Proof object conjectures             : 21
% 0.20/0.37  # Proof object clause conjectures      : 18
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 19
% 0.20/0.37  # Proof object initial formulas used   : 13
% 0.20/0.37  # Proof object generating inferences   : 10
% 0.20/0.37  # Proof object simplifying inferences  : 25
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 13
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 42
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 41
% 0.20/0.37  # Processed clauses                    : 78
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 3
% 0.20/0.37  # ...remaining for further processing  : 75
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 1
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 20
% 0.20/0.37  # ...of the previous two non-trivial   : 17
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 19
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 32
% 0.20/0.37  #    Positive orientable unit clauses  : 11
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 3
% 0.20/0.37  #    Non-unit-clauses                  : 18
% 0.20/0.37  # Current number of unprocessed clauses: 21
% 0.20/0.37  # ...number of literals in the above   : 98
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 44
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 593
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 91
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.37  # Unit Clause-clause subsumption calls : 12
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 4034
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.032 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.036 s
% 0.20/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
