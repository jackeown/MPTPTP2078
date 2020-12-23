%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 103 expanded)
%              Number of clauses        :   30 (  40 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  253 ( 697 expanded)
%              Number of equality atoms :   10 (  46 expanded)
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

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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
    ! [X24] :
      ( v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | ~ v1_xboole_0(k2_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

fof(c_0_17,plain,(
    ! [X19] :
      ( ~ l1_struct_0(X19)
      | k2_struct_0(X19) = u1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X23] :
      ( ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v4_pre_topc(k2_struct_0(X23),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_33,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_34,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_35,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_36,negated_conjecture,
    ( ~ v4_pre_topc(X1,esk4_0)
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( v4_pre_topc(k2_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
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

cnf(c_0_45,negated_conjecture,
    ( ~ v3_pre_topc(k2_struct_0(esk4_0),esk4_0)
    | ~ r2_hidden(esk5_0,k2_struct_0(esk4_0))
    | ~ m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39])])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_48,plain,(
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

cnf(c_0_49,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( ~ v3_pre_topc(u1_struct_0(esk4_0),esk4_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_46]),c_0_47])])).

cnf(c_0_51,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_39]),c_0_52]),c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_41]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t28_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 0.13/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.38  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.13/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.13/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.38  fof(fc4_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>v4_pre_topc(k2_struct_0(X1),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.13/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>~((![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X4,X3)<=>((v3_pre_topc(X4,X1)&v4_pre_topc(X4,X1))&r2_hidden(X2,X4))))&X3=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t28_connsp_2])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ![X28]:(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(((((v3_pre_topc(X28,esk4_0)|~r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0))))&(v4_pre_topc(X28,esk4_0)|~r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0)))))&(r2_hidden(esk5_0,X28)|~r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0)))))&(~v3_pre_topc(X28,esk4_0)|~v4_pre_topc(X28,esk4_0)|~r2_hidden(esk5_0,X28)|r2_hidden(X28,esk6_0)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk4_0)))))&esk6_0=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X10, X11]:(~r2_hidden(X10,X11)|~r1_tarski(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.38  fof(c_0_15, plain, ![X5]:r1_tarski(k1_xboole_0,X5), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.38  fof(c_0_16, plain, ![X24]:(v2_struct_0(X24)|~l1_struct_0(X24)|~v1_xboole_0(k2_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X19]:(~l1_struct_0(X19)|k2_struct_0(X19)=u1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.13/0.38  fof(c_0_18, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(X1,esk6_0)|~v3_pre_topc(X1,esk4_0)|~v4_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (esk6_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_24, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_25, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,k1_xboole_0)|~v4_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  fof(c_0_29, plain, ![X23]:(~v2_pre_topc(X23)|~l1_pre_topc(X23)|v4_pre_topc(k2_struct_0(X23),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_pre_topc])])).
% 0.13/0.38  cnf(c_0_30, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_33, plain, ![X22]:(~l1_pre_topc(X22)|l1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  fof(c_0_34, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.38  fof(c_0_35, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (~v4_pre_topc(X1,esk4_0)|~v3_pre_topc(X1,esk4_0)|~r2_hidden(esk5_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_37, plain, (v4_pre_topc(k2_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.13/0.38  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_42, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_43, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  fof(c_0_44, plain, ![X12, X13, X14, X15]:((((r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))|~v2_pre_topc(X12)|~l1_pre_topc(X12))&(~m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|(~r1_tarski(X13,u1_pre_topc(X12))|r2_hidden(k5_setfam_1(u1_struct_0(X12),X13),u1_pre_topc(X12)))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(X14,u1_pre_topc(X12))|~r2_hidden(X15,u1_pre_topc(X12))|r2_hidden(k9_subset_1(u1_struct_0(X12),X14,X15),u1_pre_topc(X12))))|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(m1_subset_1(esk1_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&(((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(r1_tarski(esk1_1(X12),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))&((m1_subset_1(esk2_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&((m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(((r2_hidden(esk2_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12))&(r2_hidden(esk3_1(X12),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(k9_subset_1(u1_struct_0(X12),esk2_1(X12),esk3_1(X12)),u1_pre_topc(X12))|(~r2_hidden(k5_setfam_1(u1_struct_0(X12),esk1_1(X12)),u1_pre_topc(X12))|~r2_hidden(u1_struct_0(X12),u1_pre_topc(X12)))|v2_pre_topc(X12)|~l1_pre_topc(X12)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~v3_pre_topc(k2_struct_0(esk4_0),esk4_0)|~r2_hidden(esk5_0,k2_struct_0(esk4_0))|~m1_subset_1(k2_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_39])])).
% 0.13/0.38  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.38  fof(c_0_48, plain, ![X20, X21]:((~v3_pre_topc(X21,X20)|r2_hidden(X21,u1_pre_topc(X20))|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))&(~r2_hidden(X21,u1_pre_topc(X20))|v3_pre_topc(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|~l1_pre_topc(X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (~v3_pre_topc(u1_struct_0(esk4_0),esk4_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_46]), c_0_47])])).
% 0.13/0.38  cnf(c_0_51, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_39])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_39]), c_0_52]), c_0_47])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_41]), c_0_39])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 55
% 0.13/0.38  # Proof object clause steps            : 30
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 19
% 0.13/0.38  # Proof object clause conjectures      : 16
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 17
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 20
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 39
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 38
% 0.13/0.38  # Processed clauses                    : 74
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 71
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 17
% 0.13/0.38  # ...of the previous two non-trivial   : 13
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 17
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 31
% 0.13/0.38  #    Positive orientable unit clauses  : 9
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 15
% 0.13/0.38  # ...number of literals in the above   : 74
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 41
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 718
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 93
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 9
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 1
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3832
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
