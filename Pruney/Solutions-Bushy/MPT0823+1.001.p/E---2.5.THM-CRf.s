%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0823+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:14 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 752 expanded)
%              Number of clauses        :   49 ( 335 expanded)
%              Number of leaves         :    9 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  209 (2214 expanded)
%              Number of equality atoms :   62 ( 794 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k1_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k2_relset_1(X1,X2,X3)
        & k2_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( k1_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k2_relset_1(X1,X2,X3)
          & k2_relset_1(X2,X1,k3_relset_1(X1,X2,X3)) = k1_relset_1(X1,X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t24_relset_1])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( ~ r2_hidden(X21,X20)
        | r2_hidden(k4_tarski(esk4_3(X19,X20,X21),X21),X19)
        | X20 != k2_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X24,X23),X19)
        | r2_hidden(X23,X20)
        | X20 != k2_relat_1(X19) )
      & ( ~ r2_hidden(esk5_2(X25,X26),X26)
        | ~ r2_hidden(k4_tarski(X28,esk5_2(X25,X26)),X25)
        | X26 = k2_relat_1(X25) )
      & ( r2_hidden(esk5_2(X25,X26),X26)
        | r2_hidden(k4_tarski(esk6_2(X25,X26),esk5_2(X25,X26)),X25)
        | X26 = k2_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(k4_tarski(X32,X33),X31)
        | r2_hidden(k4_tarski(X33,X32),X30)
        | X31 != k4_relat_1(X30)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(X35,X34),X30)
        | r2_hidden(k4_tarski(X34,X35),X31)
        | X31 != k4_relat_1(X30)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(k4_tarski(esk7_2(X30,X31),esk8_2(X30,X31)),X31)
        | ~ r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)
        | X31 = k4_relat_1(X30)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) )
      & ( r2_hidden(k4_tarski(esk7_2(X30,X31),esk8_2(X30,X31)),X31)
        | r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)
        | X31 = k4_relat_1(X30)
        | ~ v1_relat_1(X31)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_12,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k3_relset_1(X47,X48,X49) = k4_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

fof(c_0_13,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
    & ( k1_relset_1(esk10_0,esk9_0,k3_relset_1(esk9_0,esk10_0,esk11_0)) != k2_relset_1(esk9_0,esk10_0,esk11_0)
      | k2_relset_1(esk10_0,esk9_0,k3_relset_1(esk9_0,esk10_0,esk11_0)) != k1_relset_1(esk9_0,esk10_0,esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_16,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | m1_subset_1(k3_relset_1(X38,X39,X40),k1_zfmisc_1(k2_zfmisc_1(X39,X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_17,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k2_relset_1(X44,X45,X46) = k2_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_20,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X1),X3)
    | ~ v1_relat_1(k4_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X8,X9,X10,X12,X13,X14,X15,X17] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(k4_tarski(X10,esk1_3(X8,X9,X10)),X8)
        | X9 != k1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(X12,X13),X8)
        | r2_hidden(X12,X9)
        | X9 != k1_relat_1(X8) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r2_hidden(k4_tarski(esk2_2(X14,X15),X17),X14)
        | X15 = k1_relat_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r2_hidden(k4_tarski(esk2_2(X14,X15),esk3_2(X14,X15)),X14)
        | X15 = k1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_24,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k3_relset_1(esk9_0,esk10_0,esk11_0) = k4_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k4_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_relat_1(k4_relat_1(X2)))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k4_relat_1(esk11_0),k1_zfmisc_1(k2_zfmisc_1(esk10_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_18])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( k1_relset_1(esk10_0,esk9_0,k3_relset_1(esk9_0,esk10_0,esk11_0)) != k2_relset_1(esk9_0,esk10_0,esk11_0)
    | k2_relset_1(esk10_0,esk9_0,k3_relset_1(esk9_0,esk10_0,esk11_0)) != k1_relset_1(esk9_0,esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(esk9_0,esk10_0,esk11_0) = k2_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( k1_relset_1(esk9_0,esk10_0,esk11_0) = k1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X1),k4_relat_1(X3))
    | ~ v1_relat_1(k4_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk2_2(X2,X1),k2_relat_1(k4_relat_1(X2)))
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(esk10_0,esk9_0,k4_relat_1(esk11_0)) != k2_relat_1(esk11_0)
    | k2_relset_1(esk10_0,esk9_0,k4_relat_1(esk11_0)) != k1_relat_1(esk11_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_26]),c_0_26]),c_0_37]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k1_relset_1(esk10_0,esk9_0,k4_relat_1(esk11_0)) = k1_relat_1(k4_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_47,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(k4_relat_1(X2),k2_relat_1(k4_relat_1(X2)),X1)),X2)
    | ~ r2_hidden(X1,k2_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k1_relat_1(esk11_0)
    | r2_hidden(esk2_2(esk11_0,X1),k2_relat_1(k4_relat_1(esk11_0)))
    | r2_hidden(esk2_2(esk11_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k1_relat_1(k4_relat_1(X2)))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_52,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk10_0,esk9_0,k4_relat_1(esk11_0)) != k1_relat_1(esk11_0)
    | k1_relat_1(k4_relat_1(esk11_0)) != k2_relat_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k2_relset_1(esk10_0,esk9_0,k4_relat_1(esk11_0)) = k2_relat_1(k4_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_34])).

cnf(c_0_55,plain,
    ( X1 = k1_relat_1(X2)
    | ~ r2_hidden(esk2_2(X2,X1),k2_relat_1(k4_relat_1(X2)))
    | ~ r2_hidden(esk2_2(X2,X1),X1)
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk11_0)) = k1_relat_1(esk11_0)
    | r2_hidden(esk2_2(esk11_0,k2_relat_1(k4_relat_1(esk11_0))),k2_relat_1(k4_relat_1(esk11_0))) ),
    inference(ef,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk5_2(X2,X1),k1_relat_1(k4_relat_1(X2)))
    | r2_hidden(esk5_2(X2,X1),X1)
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk11_0)) != k1_relat_1(esk11_0)
    | k1_relat_1(k4_relat_1(esk11_0)) != k2_relat_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk11_0)) = k1_relat_1(esk11_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_42]),c_0_43])]),c_0_56])).

cnf(c_0_61,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk5_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(esk1_3(k4_relat_1(X1),k1_relat_1(k4_relat_1(X1)),X2),X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(k4_relat_1(X1)))
    | ~ v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k2_relat_1(esk11_0)
    | r2_hidden(esk5_2(esk11_0,X1),k1_relat_1(k4_relat_1(esk11_0)))
    | r2_hidden(esk5_2(esk11_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_42]),c_0_43])])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk11_0)) != k2_relat_1(esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_65,plain,
    ( X1 = k2_relat_1(X2)
    | ~ r2_hidden(esk5_2(X2,X1),k1_relat_1(k4_relat_1(X2)))
    | ~ r2_hidden(esk5_2(X2,X1),X1)
    | ~ v1_relat_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk5_2(esk11_0,k1_relat_1(k4_relat_1(esk11_0))),k1_relat_1(k4_relat_1(esk11_0))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_63]),c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_66]),c_0_42]),c_0_43])]),c_0_64]),
    [proof]).

%------------------------------------------------------------------------------
