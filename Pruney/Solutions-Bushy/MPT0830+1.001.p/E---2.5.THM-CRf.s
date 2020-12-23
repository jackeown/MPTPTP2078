%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0830+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:15 EST 2020

% Result     : Theorem 0.08s
% Output     : CNFRefutation 0.08s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 160 expanded)
%              Number of clauses        :   32 (  69 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  153 ( 432 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(redefinition_k5_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k5_relset_1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
       => m1_subset_1(k5_relset_1(X1,X3,X4,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(assume_negation,[status(cth)],[t33_relset_1])).

fof(c_0_9,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k5_relset_1(X27,X28,X29,X30) = k7_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_relset_1])])).

fof(c_0_10,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0)))
    & ~ m1_subset_1(k5_relset_1(esk5_0,esk7_0,esk8_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( k5_relset_1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X35,k1_zfmisc_1(X36))
        | r1_tarski(X35,X36) )
      & ( ~ r1_tarski(X35,X36)
        | m1_subset_1(X35,k1_zfmisc_1(X36)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_14,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( ~ r1_tarski(X18,X19)
        | ~ r2_hidden(k4_tarski(X20,X21),X18)
        | r2_hidden(k4_tarski(X20,X21),X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk3_2(X18,X22),esk4_2(X18,X22)),X18)
        | r1_tarski(X18,X22)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X18,X22),esk4_2(X18,X22)),X22)
        | r1_tarski(X18,X22)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(esk5_0,esk7_0,esk8_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( k5_relset_1(esk5_0,esk7_0,esk8_0,X1) = k7_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X12,X10)
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | X11 != k7_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(X12,X13),X9)
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | X11 != k7_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(X14,X10)
        | ~ r2_hidden(k4_tarski(X14,X15),X9)
        | r2_hidden(k4_tarski(X14,X15),X11)
        | X11 != k7_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X9,X10,X11),esk2_3(X9,X10,X11)),X11)
        | ~ r2_hidden(esk1_3(X9,X10,X11),X10)
        | ~ r2_hidden(k4_tarski(esk1_3(X9,X10,X11),esk2_3(X9,X10,X11)),X9)
        | X11 = k7_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | r2_hidden(k4_tarski(esk1_3(X9,X10,X11),esk2_3(X9,X10,X11)),X11)
        | X11 = k7_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(esk1_3(X9,X10,X11),esk2_3(X9,X10,X11)),X9)
        | r2_hidden(k4_tarski(esk1_3(X9,X10,X11),esk2_3(X9,X10,X11)),X11)
        | X11 = k7_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_21,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | v1_relat_1(k7_relat_1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk8_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k7_relat_1(X3,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)),esk4_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0))),k7_relat_1(esk8_0,esk6_0))
    | ~ v1_relat_1(k7_relat_1(esk8_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)),esk4_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0))),k7_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_28])])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)),esk4_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_28])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_34,plain,(
    ! [X31,X32,X33,X34] :
      ( ( r2_hidden(X31,X33)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( r2_hidden(X32,X34)
        | ~ r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) )
      & ( ~ r2_hidden(X31,X33)
        | ~ r2_hidden(X32,X34)
        | r2_hidden(k4_tarski(X31,X32),k2_zfmisc_1(X33,X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)),esk4_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0))),X1)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_12])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)),esk4_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0))),k2_zfmisc_1(esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k7_relat_1(X4,X2))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_26])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k2_zfmisc_1(X2,X3)),X3)
    | ~ r2_hidden(esk3_2(X1,k2_zfmisc_1(X2,X3)),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_2(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_30]),c_0_28])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0))
    | ~ v1_relat_1(k7_relat_1(esk8_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk8_0,esk6_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_26]),c_0_28])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_47]),c_0_22]),
    [proof]).

%------------------------------------------------------------------------------
