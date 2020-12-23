%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t115_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:29 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 103 expanded)
%              Number of clauses        :   29 (  42 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 525 expanded)
%              Number of equality atoms :   37 (  98 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',t115_funct_2)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',redefinition_k1_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',t5_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',cc1_relset_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',d12_funct_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',t2_subset)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t115_funct_2.p',redefinition_k7_relset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_10,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | m1_subset_1(k1_relset_1(X27,X28,X29),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_11,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_12,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | ~ v1_xboole_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_13,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | v1_relat_1(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,negated_conjecture,(
    ! [X12] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk1_0,esk2_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & r2_hidden(esk5_0,k7_relset_1(esk1_0,esk2_0,esk4_0,esk3_0))
      & ( ~ r2_hidden(X12,esk1_0)
        | ~ r2_hidden(X12,esk3_0)
        | esk5_0 != k1_funct_1(esk4_0,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( r2_hidden(esk6_4(X15,X16,X17,X18),k1_relat_1(X15))
        | ~ r2_hidden(X18,X17)
        | X17 != k9_relat_1(X15,X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk6_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k9_relat_1(X15,X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X18 = k1_funct_1(X15,esk6_4(X15,X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k9_relat_1(X15,X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X21,k1_relat_1(X15))
        | ~ r2_hidden(X21,X16)
        | X20 != k1_funct_1(X15,X21)
        | r2_hidden(X20,X17)
        | X17 != k9_relat_1(X15,X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk7_3(X15,X22,X23),X23)
        | ~ r2_hidden(X25,k1_relat_1(X15))
        | ~ r2_hidden(X25,X22)
        | esk7_3(X15,X22,X23) != k1_funct_1(X15,X25)
        | X23 = k9_relat_1(X15,X22)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk8_3(X15,X22,X23),k1_relat_1(X15))
        | r2_hidden(esk7_3(X15,X22,X23),X23)
        | X23 = k9_relat_1(X15,X22)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk8_3(X15,X22,X23),X22)
        | r2_hidden(esk7_3(X15,X22,X23),X23)
        | X23 = k9_relat_1(X15,X22)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk7_3(X15,X22,X23) = k1_funct_1(X15,esk8_3(X15,X22,X23))
        | r2_hidden(esk7_3(X15,X22,X23),X23)
        | X23 = k9_relat_1(X15,X22)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk3_0)
    | esk5_0 != k1_funct_1(esk4_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( X1 = k1_funct_1(X2,esk6_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_28,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X45,X46)
      | v1_xboole_0(X46)
      | r2_hidden(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_31,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( X1 != k9_relat_1(esk4_0,X2)
    | esk5_0 != X3
    | ~ r2_hidden(esk6_4(esk4_0,X2,X1,X3),esk1_0)
    | ~ r2_hidden(esk6_4(esk4_0,X2,X1,X3),esk3_0)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27])])).

cnf(c_0_33,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( X1 != k9_relat_1(esk4_0,esk3_0)
    | esk5_0 != X2
    | ~ r2_hidden(esk6_4(esk4_0,esk3_0,X1,X2),esk1_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27]),c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( X1 != k9_relat_1(esk4_0,esk3_0)
    | esk5_0 != X2
    | ~ r2_hidden(esk6_4(esk4_0,esk3_0,X1,X2),k1_relat_1(esk4_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_41,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k7_relset_1(X39,X40,X41,X42) = k9_relat_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_42,negated_conjecture,
    ( X1 != k9_relat_1(esk4_0,esk3_0)
    | esk5_0 != X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_27]),c_0_26])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,k7_relset_1(esk1_0,esk2_0,esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk4_0,esk3_0)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,k9_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_20])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_45,c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
