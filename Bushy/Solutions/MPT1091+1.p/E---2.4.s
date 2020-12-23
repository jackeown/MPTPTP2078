%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : finset_1__t25_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 360 expanded)
%              Number of clauses        :   31 ( 171 expanded)
%              Number of leaves         :    8 (  88 expanded)
%              Depth                    :   12
%              Number of atoms          :  114 ( 835 expanded)
%              Number of equality atoms :    3 ( 102 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',t3_subset)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',redefinition_k9_setfam_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',t100_zfmisc_1)).

fof(cc2_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_finset_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',cc2_finset_1)).

fof(fc17_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',fc17_finset_1)).

fof(t25_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
    <=> v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',t25_finset_1)).

fof(l22_finset_1,axiom,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
     => v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',l22_finset_1)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/finset_1__t25_finset_1.p',t92_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_9,plain,(
    ! [X14] : k9_setfam_1(X14) = k1_zfmisc_1(X14) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_10,plain,(
    ! [X15] : r1_tarski(X15,k1_zfmisc_1(k3_tarski(X15))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X35,X36] :
      ( ~ v1_finset_1(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | v1_finset_1(X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_finset_1])])])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_finset_1(X2)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k9_setfam_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k9_setfam_1(k3_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_18,plain,(
    ! [X37] :
      ( ~ v1_finset_1(X37)
      | v1_finset_1(k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).

cnf(c_0_19,plain,
    ( v1_finset_1(X2)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X2,k9_setfam_1(X1)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k9_setfam_1(k9_setfam_1(k3_tarski(X1)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( v1_finset_1(k1_zfmisc_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_finset_1(X1)
          & ! [X2] :
              ( r2_hidden(X2,X1)
             => v1_finset_1(X2) ) )
      <=> v1_finset_1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t25_finset_1])).

cnf(c_0_23,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k9_setfam_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( v1_finset_1(k9_setfam_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_13])).

fof(c_0_25,negated_conjecture,(
    ! [X6] :
      ( ( r2_hidden(esk2_0,esk1_0)
        | ~ v1_finset_1(esk1_0)
        | ~ v1_finset_1(k3_tarski(esk1_0)) )
      & ( ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(esk1_0)
        | ~ v1_finset_1(k3_tarski(esk1_0)) )
      & ( v1_finset_1(esk1_0)
        | v1_finset_1(k3_tarski(esk1_0)) )
      & ( ~ r2_hidden(X6,esk1_0)
        | v1_finset_1(X6)
        | v1_finset_1(k3_tarski(esk1_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])])])).

fof(c_0_26,plain,(
    ! [X12] :
      ( ( r2_hidden(esk4_1(X12),X12)
        | ~ v1_finset_1(X12)
        | v1_finset_1(k3_tarski(X12)) )
      & ( ~ v1_finset_1(esk4_1(X12))
        | ~ v1_finset_1(X12)
        | v1_finset_1(k3_tarski(X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).

cnf(c_0_27,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( v1_finset_1(esk1_0)
    | v1_finset_1(k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_29,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | r1_tarski(X33,k3_tarski(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_finset_1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_finset_1(X1)
    | v1_finset_1(k3_tarski(esk1_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_1(esk1_0),esk1_0)
    | v1_finset_1(k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k9_setfam_1(k3_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_32])).

cnf(c_0_36,plain,
    ( v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(esk4_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( v1_finset_1(esk4_1(esk1_0))
    | v1_finset_1(k3_tarski(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0)
    | ~ v1_finset_1(esk1_0)
    | ~ v1_finset_1(k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(esk1_0)
    | ~ v1_finset_1(k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( v1_finset_1(X1)
    | ~ r2_hidden(X1,X2)
    | ~ v1_finset_1(k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v1_finset_1(k3_tarski(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0)
    | ~ v1_finset_1(k3_tarski(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_31])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk1_0))
    | ~ v1_finset_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_31])])).

cnf(c_0_44,negated_conjecture,
    ( v1_finset_1(X1)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_41])])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_finset_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_41])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
