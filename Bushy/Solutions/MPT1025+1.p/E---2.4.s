%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t116_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:29 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  72 expanded)
%              Number of clauses        :   17 (  25 expanded)
%              Number of leaves         :    3 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   82 ( 386 expanded)
%              Number of equality atoms :    9 (  49 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t116_funct_2.p',t116_funct_2)).

fof(t115_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t116_funct_2.p',t115_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t116_funct_2.p',t1_subset)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

fof(c_0_4,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( r2_hidden(esk7_5(X25,X26,X27,X28,X29),X25)
        | ~ r2_hidden(X29,k7_relset_1(X25,X26,X28,X27))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( r2_hidden(esk7_5(X25,X26,X27,X28,X29),X27)
        | ~ r2_hidden(X29,k7_relset_1(X25,X26,X28,X27))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X29 = k1_funct_1(X28,esk7_5(X25,X26,X27,X28,X29))
        | ~ r2_hidden(X29,k7_relset_1(X25,X26,X28,X27))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t115_funct_2])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X12] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk1_0,esk2_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & r2_hidden(esk5_0,k7_relset_1(esk1_0,esk2_0,esk4_0,esk3_0))
      & ( ~ m1_subset_1(X12,esk1_0)
        | ~ r2_hidden(X12,esk3_0)
        | esk5_0 != k1_funct_1(esk4_0,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(esk7_5(X1,X2,X3,X4,X5),X1)
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X1 = k1_funct_1(X2,esk7_5(X3,X4,X5,X2,X1))
    | ~ r2_hidden(X1,k7_relset_1(X3,X4,X2,X5))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( r2_hidden(esk7_5(X1,X2,X3,X4,X5),X3)
    | ~ r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_12,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | m1_subset_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk7_5(esk1_0,esk2_0,X1,esk4_0,X2),esk1_0)
    | ~ r2_hidden(X2,k7_relset_1(esk1_0,esk2_0,esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_0,k7_relset_1(esk1_0,esk2_0,esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(esk4_0,esk7_5(esk1_0,esk2_0,X1,esk4_0,X2)) = X2
    | ~ r2_hidden(X2,k7_relset_1(esk1_0,esk2_0,esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_7]),c_0_8]),c_0_9])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk7_5(esk1_0,esk2_0,X1,esk4_0,X2),X1)
    | ~ r2_hidden(X2,k7_relset_1(esk1_0,esk2_0,esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_7]),c_0_8]),c_0_9])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( ~ m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X1,esk3_0)
    | esk5_0 != k1_funct_1(esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk4_0,esk7_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0)) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk7_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_5(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
