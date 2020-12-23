%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : pre_topc__t5_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:45 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   24 (  40 expanded)
%              Number of clauses        :   12 (  16 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :  143 ( 176 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t5_pre_topc.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t5_pre_topc.p',t2_xboole_1)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t5_pre_topc.p',redefinition_k5_setfam_1)).

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
    file('/export/starexec/sandbox/benchmark/pre_topc__t5_pre_topc.p',d1_pre_topc)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t5_pre_topc.p',t2_zfmisc_1)).

fof(t5_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t5_pre_topc.p',t5_pre_topc)).

fof(c_0_6,plain,(
    ! [X45,X46] :
      ( ( ~ m1_subset_1(X45,k1_zfmisc_1(X46))
        | r1_tarski(X45,X46) )
      & ( ~ r1_tarski(X45,X46)
        | m1_subset_1(X45,k1_zfmisc_1(X46)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_7,plain,(
    ! [X44] : r1_tarski(k1_xboole_0,X44) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_8,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(X34)))
      | k5_setfam_1(X34,X35) = k3_tarski(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_9,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
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
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk4_1(X12),u1_pre_topc(X12))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))
        | m1_subset_1(esk2_1(X12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X12))))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk4_1(X12),u1_pre_topc(X12))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))
        | r1_tarski(esk2_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk3_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk4_1(X12),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk3_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( r2_hidden(esk4_1(X12),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X12),esk3_1(X12),esk4_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X12),esk2_1(X12)),u1_pre_topc(X12))
        | ~ r2_hidden(u1_struct_0(X12),u1_pre_topc(X12))
        | v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_12,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    inference(assume_negation,[status(cth)],[t5_pre_topc])).

cnf(c_0_16,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k5_setfam_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_10]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
