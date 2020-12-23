%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_1__t69_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:31 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   44 (  75 expanded)
%              Number of clauses        :   25 (  30 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 205 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    9 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_tops_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
           => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',t69_tops_1)).

fof(t52_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v4_pre_topc(X2,X1)
             => k2_pre_topc(X1,X2) = X2 )
            & ( ( v2_pre_topc(X1)
                & k2_pre_topc(X1,X2) = X2 )
             => v4_pre_topc(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',t52_pre_topc)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',redefinition_k9_subset_1)).

fof(d2_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',d2_tops_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',commutativity_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',commutativity_k3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t69_tops_1.p',t3_subset)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v4_pre_topc(X2,X1)
             => r1_tarski(k2_tops_1(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_tops_1])).

fof(c_0_10,plain,(
    ! [X68,X69] :
      ( ( ~ v4_pre_topc(X69,X68)
        | k2_pre_topc(X68,X69) = X69
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ l1_pre_topc(X68) )
      & ( ~ v2_pre_topc(X68)
        | k2_pre_topc(X68,X69) != X69
        | v4_pre_topc(X69,X68)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | ~ l1_pre_topc(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_pre_topc])])])])).

fof(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & v4_pre_topc(esk2_0,esk1_0)
    & ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(X37))
      | m1_subset_1(k9_subset_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X53,X54,X55] :
      ( ~ m1_subset_1(X55,k1_zfmisc_1(X53))
      | k9_subset_1(X53,X54,X55) = k3_xboole_0(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | k2_tops_1(X14,X15) = k9_subset_1(u1_struct_0(X14),k2_pre_topc(X14,X15),k2_pre_topc(X14,k3_subset_1(u1_struct_0(X14),X15))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_1])])])).

cnf(c_0_15,plain,
    ( k2_pre_topc(X2,X1) = X1
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v4_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X11))
      | k9_subset_1(X11,X12,X13) = k9_subset_1(X11,X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_20,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_23,plain,
    ( k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( k2_pre_topc(esk1_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X16,X17)
        | ~ r2_hidden(X18,X16)
        | r2_hidden(X18,X17) )
      & ( r2_hidden(esk3_2(X19,X20),X19)
        | r1_tarski(X19,X20) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | r1_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_27,plain,(
    ! [X62,X63] :
      ( ( ~ m1_subset_1(X62,k1_zfmisc_1(X63))
        | r1_tarski(X62,X63) )
      & ( ~ r1_tarski(X62,X63)
        | m1_subset_1(X62,k1_zfmisc_1(X63)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk1_0),esk2_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k2_tops_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18]),c_0_17])])).

cnf(c_0_31,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(esk1_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k3_xboole_0(esk2_0,k2_pre_topc(esk1_0,k3_subset_1(u1_struct_0(esk1_0),esk2_0))) = k2_tops_1(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_18])]),c_0_29])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_tops_1(esk1_0,esk2_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
