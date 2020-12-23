%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1091+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:43 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 239 expanded)
%              Number of clauses        :   22 ( 108 expanded)
%              Number of leaves         :    7 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :   97 ( 725 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_finset_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_finset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(fc17_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(t25_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
    <=> v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(t92_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(l22_finset_1,axiom,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
     => v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(c_0_7,plain,(
    ! [X3,X4] :
      ( ~ v1_finset_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_finset_1(X4) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_finset_1])])])).

fof(c_0_8,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_9,plain,
    ( v1_finset_1(X2)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X9] : r1_tarski(X9,k1_zfmisc_1(k3_tarski(X9))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_12,plain,
    ( v1_finset_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X5] :
      ( ~ v1_finset_1(X5)
      | v1_finset_1(k1_zfmisc_1(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_finset_1(X1)
          & ! [X2] :
              ( r2_hidden(X2,X1)
             => v1_finset_1(X2) ) )
      <=> v1_finset_1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t25_finset_1])).

cnf(c_0_16,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( v1_finset_1(k1_zfmisc_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ! [X16] :
      ( ( r2_hidden(esk3_0,esk2_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ v1_finset_1(esk3_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( v1_finset_1(esk2_0)
        | v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ r2_hidden(X16,esk2_0)
        | v1_finset_1(X16)
        | v1_finset_1(k3_tarski(esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | r1_tarski(X12,k3_tarski(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t92_zfmisc_1])])).

cnf(c_0_20,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_finset_1(esk2_0)
    | v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_finset_1(esk3_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X6] :
      ( ( r2_hidden(esk1_1(X6),X6)
        | ~ v1_finset_1(X6)
        | v1_finset_1(k3_tarski(X6)) )
      & ( ~ v1_finset_1(esk1_1(X6))
        | ~ v1_finset_1(X6)
        | v1_finset_1(k3_tarski(X6)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).

cnf(c_0_27,plain,
    ( v1_finset_1(X1)
    | ~ r2_hidden(X1,X2)
    | ~ v1_finset_1(k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk2_0))
    | ~ v1_finset_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_24])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( v1_finset_1(X1)
    | v1_finset_1(k3_tarski(esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_1(esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_31])).

cnf(c_0_34,plain,
    ( v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(esk1_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_finset_1(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24])]),c_0_31]),
    [proof]).

%------------------------------------------------------------------------------
