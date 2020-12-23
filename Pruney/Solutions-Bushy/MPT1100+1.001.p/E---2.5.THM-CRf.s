%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1100+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:43 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   25 (  40 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :  149 ( 181 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(t5_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11)))
      | k5_setfam_1(X11,X12) = k3_tarski(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_7,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_8,plain,(
    ! [X4,X5,X6,X7] :
      ( ( r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r1_tarski(X5,u1_pre_topc(X4))
        | r2_hidden(k5_setfam_1(u1_struct_0(X4),X5),u1_pre_topc(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ r2_hidden(X6,u1_pre_topc(X4))
        | ~ r2_hidden(X7,u1_pre_topc(X4))
        | r2_hidden(k9_subset_1(u1_struct_0(X4),X6,X7),u1_pre_topc(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk2_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk3_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk2_1(X4),u1_pre_topc(X4))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk3_1(X4),u1_pre_topc(X4))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X4),esk2_1(X4),esk3_1(X4)),u1_pre_topc(X4))
        | m1_subset_1(esk1_1(X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk2_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk3_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk2_1(X4),u1_pre_topc(X4))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk3_1(X4),u1_pre_topc(X4))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X4),esk2_1(X4),esk3_1(X4)),u1_pre_topc(X4))
        | r1_tarski(esk1_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk2_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( m1_subset_1(esk3_1(X4),k1_zfmisc_1(u1_struct_0(X4)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk2_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( r2_hidden(esk3_1(X4),u1_pre_topc(X4))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X4),esk2_1(X4),esk3_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X4),esk1_1(X4)),u1_pre_topc(X4))
        | ~ r2_hidden(u1_struct_0(X4),u1_pre_topc(X4))
        | v2_pre_topc(X4)
        | ~ l1_pre_topc(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_9,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_12,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k5_setfam_1(X1,X2) = k3_tarski(X2)
    | ~ r1_tarski(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    inference(assume_negation,[status(cth)],[t5_pre_topc])).

cnf(c_0_17,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
    | ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_18,plain,
    ( k5_setfam_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),c_0_23]),
    [proof]).

%------------------------------------------------------------------------------
