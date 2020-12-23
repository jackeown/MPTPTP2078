%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t35_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:09 EDT 2019

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :   49 (  88 expanded)
%              Number of clauses        :   30 (  39 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 273 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_relset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',t35_relset_1)).

fof(redefinition_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k6_relset_1(X1,X2,X3,X4) = k8_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',redefinition_k6_relset_1)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',d12_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',d3_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',t3_subset)).

fof(dt_k6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k6_relset_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',dt_k6_relset_1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',t106_zfmisc_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t35_relset_1.p',dt_k8_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
       => m1_subset_1(k6_relset_1(X3,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t35_relset_1])).

fof(c_0_10,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k6_relset_1(X36,X37,X38,X39) = k8_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_relset_1])])).

fof(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X16,X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(X15,X16),X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X18,X12)
        | ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | ~ r2_hidden(esk6_3(X12,X13,X14),X12)
        | ~ r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X13)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk6_3(X12,X13,X14),X12)
        | r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X13)
        | r2_hidden(k4_tarski(esk5_3(X12,X13,X14),esk6_3(X12,X13,X14)),X14)
        | X14 = k8_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_13,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r1_tarski(X21,X22)
        | ~ r2_hidden(k4_tarski(X23,X24),X21)
        | r2_hidden(k4_tarski(X23,X24),X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk7_2(X21,X25),esk8_2(X21,X25)),X21)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk7_2(X21,X25),esk8_2(X21,X25)),X25)
        | r1_tarski(X21,X25)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X61,X62,X63] :
      ( ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))
      | v1_relat_1(X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_15,plain,(
    ! [X48,X49] :
      ( ( ~ m1_subset_1(X48,k1_zfmisc_1(X49))
        | r1_tarski(X48,X49) )
      & ( ~ r1_tarski(X48,X49)
        | m1_subset_1(X48,k1_zfmisc_1(X49)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_16,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | m1_subset_1(k6_relset_1(X28,X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_relset_1])])).

cnf(c_0_17,plain,
    ( k6_relset_1(X2,X3,X4,X1) = k8_relat_1(X4,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X40,X41,X42,X43] :
      ( ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( r2_hidden(X41,X43)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( ~ r2_hidden(X40,X42)
        | ~ r2_hidden(X41,X43)
        | r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | v1_relat_1(k8_relat_1(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( m1_subset_1(k6_relset_1(X2,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k6_relset_1(esk3_0,esk1_0,X1,esk4_0) = k8_relat_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk8_2(X1,X2),X3)
    | X1 != k8_relat_1(X3,X4)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk8_2(X1,X2)),X3)
    | ~ r1_tarski(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k8_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_18])])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk8_2(X1,k2_zfmisc_1(X2,X3)),X3)
    | ~ r2_hidden(esk7_2(X1,k2_zfmisc_1(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k8_relat_1(X1,X2),X3)
    | r2_hidden(esk8_2(k8_relat_1(X1,X2),X3),X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk7_2(X1,X2),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),k2_zfmisc_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(k6_relset_1(esk3_0,esk1_0,esk2_0,esk4_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_43,plain,
    ( r1_tarski(k8_relat_1(X1,X2),k2_zfmisc_1(X3,X1))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk7_2(k8_relat_1(X1,X2),k2_zfmisc_1(X3,X1)),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),X2)
    | r2_hidden(esk7_2(k8_relat_1(X1,esk4_0),X2),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk2_0,esk4_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k8_relat_1(X1,esk4_0),k2_zfmisc_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
