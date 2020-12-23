%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:38 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (  99 expanded)
%              Number of clauses        :   29 (  38 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :  250 ( 688 expanded)
%              Number of equality atoms :   10 (  43 expanded)
%              Maximal formula depth    :   27 (   4 average)
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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc4_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => v4_pre_topc(k2_struct_0(X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,negated_conjecture,(
    ! [X28] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
      & ( v3_pre_topc(X28,esk4_0)
        | ~ r2_hidden(X28,esk6_0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( v4_pre_topc(X28,esk4_0)
        | ~ r2_hidden(X28,esk6_0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( r2_hidden(esk5_0,X28)
        | ~ r2_hidden(X28,esk6_0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( ~ v3_pre_topc(X28,esk4_0)
        | ~ v4_pre_topc(X28,esk4_0)
        | ~ r2_hidden(esk5_0,X28)
        | r2_hidden(X28,esk6_0)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & esk6_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | ~ r1_tarski(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_15,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_16,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X23] :
      ( v2_struct_0(X23)
      | ~ l1_struct_0(X23)
      | ~ v1_xboole_0(u1_struct_0(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,plain,(
    ! [X24] :
      ( ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v4_pre_topc(k2_struct_0(X24),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_31,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_32,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_33,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_37,plain,(
    ! [X19] :
      ( ~ l1_struct_0(X19)
      | k2_struct_0(X19) = u1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X12,X13,X14,X15] :
      ( ( r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r1_tarski(X13,u1_pre_topc(X12))
        | r2_hidden(k5_setfam_1(u1_struct_0(X12),X13),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(X14,u1_pre_topc(X12))
        | ~ r2_hidden(X15,u1_pre_topc(X12))
        | r2_hidden(k9_subset_1(u1_struct_0(X12),X14,X15),u1_pre_topc(X12))
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))
        | m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))
        | r1_tarski(esk1_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v3_pre_topc(k2_struct_0(esk4_0),esk4_0)
    | ~ r2_hidden(esk5_0,k2_struct_0(esk4_0))
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_44,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_36])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,plain,(
    ! [X20,X21] :
      ( ( ~ v3_pre_topc(X21,X20)
        | r2_hidden(X21,u1_pre_topc(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) )
      & ( ~ r2_hidden(X21,u1_pre_topc(X20))
        | v3_pre_topc(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_48,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk4_0),esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_50,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_36])])).

cnf(c_0_52,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_36]),c_0_51]),c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_39]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.13/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.37  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.13/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.37  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.37  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.37  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.37  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.13/0.37  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.13/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.13/0.37  fof(c_0_13, negated_conjecture, ![X28]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(((((v3_pre_topc(X28,esk4_0)|~r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0))))&(v4_pre_topc(X28,esk4_0)|~r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0)))))&(r2_hidden(esk5_0,X28)|~r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0)))))&(~v3_pre_topc(X28,esk4_0)|~v4_pre_topc(X28,esk4_0)|~r2_hidden(esk5_0,X28)|r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0)))))&esk6_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.13/0.37  fof(c_0_14, plain, ![X10, X11]:(~r2_hidden(X10,X11)|~r1_tarski(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.37  fof(c_0_15, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.37  fof(c_0_16, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk6_0)|~v3_pre_topc(X1,esk4_0)|~v4_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (esk6_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_20, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_21, plain, ![X23]:(v2_struct_0(X23)|~l1_struct_0(X23)|~v1_xboole_0(u1_struct_0(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.37  cnf(c_0_22, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v4_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_25, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  fof(c_0_26, plain, ![X24]:(~v2_pre_topc(X24)|~l1_pre_topc(X24)|v4_pre_topc(k2_struct_0(X24),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.13/0.37  cnf(c_0_27, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  fof(c_0_30, plain, ![X22]:(~l1_pre_topc(X22)|l1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.37  fof(c_0_31, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.37  fof(c_0_32, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (~v4_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.37  cnf(c_0_34, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  fof(c_0_37, plain, ![X19]:(~l1_struct_0(X19)|k2_struct_0(X19)=u1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.13/0.37  cnf(c_0_39, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.37  cnf(c_0_40, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.37  cnf(c_0_41, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.37  fof(c_0_42, plain, ![X12, X13, X14, X15]:((((r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))|~v2_pre_topc(X12)|~l1_pre_topc(X12))&(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|(~r1_tarski(X13,u1_pre_topc(X12))|r2_hidden(k5_setfam_1(u1_struct_0(X12),X13),u1_pre_topc(X12)))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(X14,u1_pre_topc(X12))|~r2_hidden(X15,u1_pre_topc(X12))|r2_hidden(k9_subset_1(u1_struct_0(X12),X14,X15),u1_pre_topc(X12))))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&(((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (~v3_pre_topc(k2_struct_0(esk4_0),esk4_0)|~r2_hidden(esk5_0,k2_struct_0(esk4_0))|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.37  cnf(c_0_44, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_36])])).
% 0.13/0.37  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  fof(c_0_47, plain, ![X20, X21]:((~v3_pre_topc(X21,X20)|r2_hidden(X21,u1_pre_topc(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(~r2_hidden(X21,u1_pre_topc(X20))|v3_pre_topc(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.13/0.37  cnf(c_0_48, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk4_0),esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.13/0.37  cnf(c_0_50, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_36])])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_36]), c_0_51]), c_0_46])])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_39]), c_0_36])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 54
% 0.13/0.37  # Proof object clause steps            : 29
% 0.13/0.37  # Proof object formula steps           : 25
% 0.13/0.37  # Proof object conjectures             : 19
% 0.13/0.37  # Proof object clause conjectures      : 16
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 12
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 20
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 12
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 39
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 38
% 0.13/0.37  # Processed clauses                    : 75
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 3
% 0.13/0.37  # ...remaining for further processing  : 72
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 2
% 0.13/0.37  # Generated clauses                    : 18
% 0.13/0.37  # ...of the previous two non-trivial   : 12
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 18
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 32
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 20
% 0.13/0.37  # Current number of unprocessed clauses: 13
% 0.13/0.37  # ...number of literals in the above   : 64
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 41
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 727
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 76
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 9
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 2
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3927
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
