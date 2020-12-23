%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 919 expanded)
%              Number of clauses        :   58 ( 394 expanded)
%              Number of leaves         :   10 ( 218 expanded)
%              Depth                    :   16
%              Number of atoms          :  241 (4595 expanded)
%              Number of equality atoms :    4 ( 144 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ~ v1_xboole_0(X3)
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                      <=> ? [X6] :
                            ( m1_subset_1(X6,X3)
                            & r2_hidden(k4_tarski(X6,X5),X4)
                            & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ~ v1_xboole_0(X3)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,X3)
                              & r2_hidden(k4_tarski(X6,X5),X4)
                              & r2_hidden(X6,X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relset_1])).

fof(c_0_11,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k7_relset_1(X33,X34,X35,X36) = k9_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X42] :
      ( ~ v1_xboole_0(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))
      & m1_subset_1(esk7_0,esk3_0)
      & ( ~ r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))
        | ~ m1_subset_1(X42,esk5_0)
        | ~ r2_hidden(k4_tarski(X42,esk7_0),esk6_0)
        | ~ r2_hidden(X42,esk4_0) )
      & ( m1_subset_1(esk8_0,esk5_0)
        | r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) )
      & ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)
        | r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) )
      & ( r2_hidden(esk8_0,esk4_0)
        | r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).

cnf(c_0_13,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X18,X19] :
      ( ~ r2_hidden(X18,X19)
      | m1_subset_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_16,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X22,X23,X24,X26] :
      ( ( r2_hidden(esk2_3(X22,X23,X24),k1_relat_1(X24))
        | ~ r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk2_3(X22,X23,X24),X22),X24)
        | ~ r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X23)
        | ~ r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X26,k1_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X26,X22),X24)
        | ~ r2_hidden(X26,X23)
        | r2_hidden(X22,k9_relat_1(X24,X23))
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)
    | r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k7_relset_1(esk5_0,esk3_0,esk6_0,X1) = k9_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(X28,k2_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)
    | r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_29,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X20,X21)
      | v1_xboole_0(X21)
      | r2_hidden(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))
    | r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_14])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | ~ r2_hidden(k4_tarski(X1,esk7_0),esk6_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0)
    | r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)
    | ~ v1_xboole_0(k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | v1_xboole_0(X2)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | m1_subset_1(k4_tarski(esk8_0,esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | r2_hidden(esk8_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk8_0,esk5_0)
    | r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)
    | ~ v1_xboole_0(k9_relat_1(esk6_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0)
    | ~ v1_xboole_0(k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | r2_hidden(esk7_0,k9_relat_1(esk6_0,X1))
    | ~ r2_hidden(esk8_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_34])]),c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0)
    | ~ m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))
    | r2_hidden(esk8_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))
    | m1_subset_1(esk8_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk7_0,k9_relat_1(esk6_0,X1))
    | ~ r2_hidden(esk8_0,X1)
    | ~ v1_xboole_0(k9_relat_1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_34])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,esk4_0)
    | ~ v1_xboole_0(k9_relat_1(esk6_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk8_0,esk5_0)
    | ~ v1_xboole_0(k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_46])).

fof(c_0_56,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ r2_hidden(X17,X16)
      | r2_hidden(X17,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | ~ m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_49]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | r2_hidden(esk8_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))
    | m1_subset_1(esk8_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( ~ m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ v1_xboole_0(k9_relat_1(esk6_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_53]),c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k4_tarski(esk8_0,esk7_0),esk6_0)
    | ~ v1_xboole_0(k9_relat_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk8_0,esk5_0)
    | ~ v1_xboole_0(k9_relat_1(esk6_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_55,c_0_19])).

fof(c_0_63,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_hidden(X11,X13)
        | ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) )
      & ( r2_hidden(X12,X14)
        | ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) )
      & ( ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X12,X14)
        | r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_64,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_43]),c_0_58]),c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k9_relat_1(esk6_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_54]),c_0_62])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk3_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( ~ m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_65])]),c_0_66])).

cnf(c_0_70,plain,
    ( m1_subset_1(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk7_0,X1,esk6_0),esk5_0)
    | ~ r2_hidden(esk2_3(esk7_0,X1,esk6_0),esk4_0)
    | ~ r2_hidden(esk7_0,k9_relat_1(esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_34])])).

cnf(c_0_73,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_24]),c_0_34])])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk7_0,esk4_0,esk6_0),esk5_0)
    | ~ r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_34])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_3(X1,X2,esk6_0),esk5_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_36]),c_0_65])]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:04:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.027 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t52_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 0.19/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.39  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.39  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.19/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.39  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(~(v1_xboole_0(X3))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>![X5]:(m1_subset_1(X5,X1)=>(r2_hidden(X5,k7_relset_1(X3,X1,X4,X2))<=>?[X6]:((m1_subset_1(X6,X3)&r2_hidden(k4_tarski(X6,X5),X4))&r2_hidden(X6,X2))))))))), inference(assume_negation,[status(cth)],[t52_relset_1])).
% 0.19/0.39  fof(c_0_11, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k7_relset_1(X33,X34,X35,X36)=k9_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.39  fof(c_0_12, negated_conjecture, ![X42]:(~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))&(m1_subset_1(esk7_0,esk3_0)&((~r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))|(~m1_subset_1(X42,esk5_0)|~r2_hidden(k4_tarski(X42,esk7_0),esk6_0)|~r2_hidden(X42,esk4_0)))&(((m1_subset_1(esk8_0,esk5_0)|r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)))&(r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)|r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))))&(r2_hidden(esk8_0,esk4_0)|r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0)))))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])])).
% 0.19/0.39  cnf(c_0_13, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  fof(c_0_15, plain, ![X18, X19]:(~r2_hidden(X18,X19)|m1_subset_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.39  fof(c_0_16, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.39  fof(c_0_17, plain, ![X22, X23, X24, X26]:((((r2_hidden(esk2_3(X22,X23,X24),k1_relat_1(X24))|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk2_3(X22,X23,X24),X22),X24)|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24)))&(r2_hidden(esk2_3(X22,X23,X24),X23)|~r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24)))&(~r2_hidden(X26,k1_relat_1(X24))|~r2_hidden(k4_tarski(X26,X22),X24)|~r2_hidden(X26,X23)|r2_hidden(X22,k9_relat_1(X24,X23))|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)|r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (k7_relset_1(esk5_0,esk3_0,esk6_0,X1)=k9_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.39  fof(c_0_20, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.39  fof(c_0_21, plain, ![X27, X28, X29]:((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))&(r2_hidden(X28,k2_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.19/0.39  cnf(c_0_22, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_24, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)|r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.39  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_27, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_28, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  fof(c_0_29, plain, ![X20, X21]:(~m1_subset_1(X20,X21)|(v1_xboole_0(X21)|r2_hidden(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))|r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))|~m1_subset_1(X1,esk5_0)|~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_32, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_25])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_14])).
% 0.19/0.39  cnf(c_0_35, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.39  cnf(c_0_36, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))|r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)), inference(rw,[status(thm)],[c_0_30, c_0_19])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))|~r2_hidden(k4_tarski(X1,esk7_0),esk6_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[c_0_31, c_0_19])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_0,esk4_0)|r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)|~v1_xboole_0(k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.19/0.39  cnf(c_0_42, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|v1_xboole_0(X2)|~v1_relat_1(X2)|~m1_subset_1(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))|m1_subset_1(k4_tarski(esk8_0,esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_37])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (~m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)|~m1_subset_1(X1,esk5_0)|~r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_39])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))|r2_hidden(esk8_0,esk4_0)), inference(rw,[status(thm)],[c_0_40, c_0_19])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk8_0,esk5_0)|r2_hidden(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk7_0),esk6_0)|~v1_xboole_0(k9_relat_1(esk6_0,esk4_0))), inference(rw,[status(thm)],[c_0_41, c_0_19])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (r2_hidden(esk8_0,esk4_0)|~v1_xboole_0(k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_40])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))|r2_hidden(esk7_0,k9_relat_1(esk6_0,X1))|~r2_hidden(esk8_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_34])]), c_0_39])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (r2_hidden(esk8_0,esk4_0)|~m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)|~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))|r2_hidden(esk8_0,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_40])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk7_0,k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))|m1_subset_1(esk8_0,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_46])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (r2_hidden(esk7_0,k9_relat_1(esk6_0,X1))|~r2_hidden(esk8_0,X1)|~v1_xboole_0(k9_relat_1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_47]), c_0_34])])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(esk8_0,esk4_0)|~v1_xboole_0(k9_relat_1(esk6_0,esk4_0))), inference(rw,[status(thm)],[c_0_48, c_0_19])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk8_0,esk5_0)|~v1_xboole_0(k7_relset_1(esk5_0,esk3_0,esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_46])).
% 0.19/0.39  fof(c_0_56, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|(~r2_hidden(X17,X16)|r2_hidden(X17,X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))|~m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)|~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_49]), c_0_50])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))|r2_hidden(esk8_0,esk4_0)), inference(rw,[status(thm)],[c_0_51, c_0_19])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))|m1_subset_1(esk8_0,esk5_0)), inference(rw,[status(thm)],[c_0_52, c_0_19])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (~m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)|~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk4_0)|~v1_xboole_0(k9_relat_1(esk6_0,esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_53]), c_0_54])).
% 0.19/0.39  cnf(c_0_61, negated_conjecture, (m1_subset_1(k4_tarski(esk8_0,esk7_0),esk6_0)|~v1_xboole_0(k9_relat_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_47])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk8_0,esk5_0)|~v1_xboole_0(k9_relat_1(esk6_0,esk4_0))), inference(rw,[status(thm)],[c_0_55, c_0_19])).
% 0.19/0.39  fof(c_0_63, plain, ![X11, X12, X13, X14]:(((r2_hidden(X11,X13)|~r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)))&(r2_hidden(X12,X14)|~r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14))))&(~r2_hidden(X11,X13)|~r2_hidden(X12,X14)|r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.39  cnf(c_0_64, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk7_0,k9_relat_1(esk6_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_43]), c_0_58]), c_0_59])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(k9_relat_1(esk6_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_54]), c_0_62])).
% 0.19/0.39  cnf(c_0_67, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk3_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_14])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (~m1_subset_1(k4_tarski(X1,esk7_0),esk6_0)|~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_65])]), c_0_66])).
% 0.19/0.39  cnf(c_0_70, plain, (m1_subset_1(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_22, c_0_24])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(k4_tarski(X1,X2),esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (~m1_subset_1(esk2_3(esk7_0,X1,esk6_0),esk5_0)|~r2_hidden(esk2_3(esk7_0,X1,esk6_0),esk4_0)|~r2_hidden(esk7_0,k9_relat_1(esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_34])])).
% 0.19/0.39  cnf(c_0_73, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_74, negated_conjecture, (r2_hidden(esk2_3(X1,X2,esk6_0),esk5_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_24]), c_0_34])])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (~m1_subset_1(esk2_3(esk7_0,esk4_0,esk6_0),esk5_0)|~r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_34])])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk2_3(X1,X2,esk6_0),esk5_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_22, c_0_74])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk7_0,k9_relat_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.39  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_36]), c_0_65])]), c_0_66]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 79
% 0.19/0.39  # Proof object clause steps            : 58
% 0.19/0.39  # Proof object formula steps           : 21
% 0.19/0.39  # Proof object conjectures             : 46
% 0.19/0.39  # Proof object clause conjectures      : 43
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 10
% 0.19/0.39  # Proof object generating inferences   : 32
% 0.19/0.39  # Proof object simplifying inferences  : 36
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 10
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 25
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 25
% 0.19/0.39  # Processed clauses                    : 415
% 0.19/0.39  # ...of these trivial                  : 16
% 0.19/0.39  # ...subsumed                          : 188
% 0.19/0.39  # ...remaining for further processing  : 211
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 28
% 0.19/0.39  # Backward-rewritten                   : 24
% 0.19/0.39  # Generated clauses                    : 752
% 0.19/0.39  # ...of the previous two non-trivial   : 711
% 0.19/0.39  # Contextual simplify-reflections      : 14
% 0.19/0.39  # Paramodulations                      : 746
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 153
% 0.19/0.39  #    Positive orientable unit clauses  : 9
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 9
% 0.19/0.39  #    Non-unit-clauses                  : 135
% 0.19/0.39  # Current number of unprocessed clauses: 299
% 0.19/0.39  # ...number of literals in the above   : 1412
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 58
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 4072
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 2009
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 105
% 0.19/0.39  # Unit Clause-clause subsumption calls : 134
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 5
% 0.19/0.39  # BW rewrite match successes           : 5
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 13317
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.052 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.056 s
% 0.19/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
