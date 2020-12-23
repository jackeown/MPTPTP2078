%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1100+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:01 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   23 (  32 expanded)
%              Number of clauses        :   11 (  12 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :  137 ( 158 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',redefinition_k5_setfam_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',t4_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT004+2.ax',t2_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT002+2.ax',t2_xboole_1)).

fof(t5_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(c_0_6,plain,(
    ! [X2789,X2790] :
      ( ~ m1_subset_1(X2790,k1_zfmisc_1(k1_zfmisc_1(X2789)))
      | k5_setfam_1(X2789,X2790) = k3_tarski(X2790) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_7,plain,(
    ! [X754] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X754)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_8,plain,(
    ! [X662,X663,X664,X665] :
      ( ( r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | ~ v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( ~ m1_subset_1(X663,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X662))))
        | ~ r1_tarski(X663,u1_pre_topc(X662))
        | r2_hidden(k5_setfam_1(u1_struct_0(X662),X663),u1_pre_topc(X662))
        | ~ v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( ~ m1_subset_1(X664,k1_zfmisc_1(u1_struct_0(X662)))
        | ~ m1_subset_1(X665,k1_zfmisc_1(u1_struct_0(X662)))
        | ~ r2_hidden(X664,u1_pre_topc(X662))
        | ~ r2_hidden(X665,u1_pre_topc(X662))
        | r2_hidden(k9_subset_1(u1_struct_0(X662),X664,X665),u1_pre_topc(X662))
        | ~ v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( m1_subset_1(esk118_1(X662),k1_zfmisc_1(u1_struct_0(X662)))
        | m1_subset_1(esk117_1(X662),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X662))))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( m1_subset_1(esk119_1(X662),k1_zfmisc_1(u1_struct_0(X662)))
        | m1_subset_1(esk117_1(X662),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X662))))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( r2_hidden(esk118_1(X662),u1_pre_topc(X662))
        | m1_subset_1(esk117_1(X662),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X662))))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( r2_hidden(esk119_1(X662),u1_pre_topc(X662))
        | m1_subset_1(esk117_1(X662),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X662))))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X662),esk118_1(X662),esk119_1(X662)),u1_pre_topc(X662))
        | m1_subset_1(esk117_1(X662),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X662))))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( m1_subset_1(esk118_1(X662),k1_zfmisc_1(u1_struct_0(X662)))
        | r1_tarski(esk117_1(X662),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( m1_subset_1(esk119_1(X662),k1_zfmisc_1(u1_struct_0(X662)))
        | r1_tarski(esk117_1(X662),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( r2_hidden(esk118_1(X662),u1_pre_topc(X662))
        | r1_tarski(esk117_1(X662),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( r2_hidden(esk119_1(X662),u1_pre_topc(X662))
        | r1_tarski(esk117_1(X662),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X662),esk118_1(X662),esk119_1(X662)),u1_pre_topc(X662))
        | r1_tarski(esk117_1(X662),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( m1_subset_1(esk118_1(X662),k1_zfmisc_1(u1_struct_0(X662)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X662),esk117_1(X662)),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( m1_subset_1(esk119_1(X662),k1_zfmisc_1(u1_struct_0(X662)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X662),esk117_1(X662)),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( r2_hidden(esk118_1(X662),u1_pre_topc(X662))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X662),esk117_1(X662)),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( r2_hidden(esk119_1(X662),u1_pre_topc(X662))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X662),esk117_1(X662)),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X662),esk118_1(X662),esk119_1(X662)),u1_pre_topc(X662))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X662),esk117_1(X662)),u1_pre_topc(X662))
        | ~ r2_hidden(u1_struct_0(X662),u1_pre_topc(X662))
        | v2_pre_topc(X662)
        | ~ l1_pre_topc(X662) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_9,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

fof(c_0_12,plain,(
    ! [X680] : r1_tarski(k1_xboole_0,X680) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    inference(assume_negation,[status(cth)],[t5_pre_topc])).

cnf(c_0_14,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k5_setfam_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_18,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_15]),c_0_16])])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
