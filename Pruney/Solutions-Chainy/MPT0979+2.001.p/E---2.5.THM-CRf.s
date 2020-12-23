%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   63 (26307 expanded)
%              Number of clauses        :   52 (9724 expanded)
%              Number of leaves         :    5 (6277 expanded)
%              Depth                    :   23
%              Number of atoms          :  238 (215338 expanded)
%              Number of equality atoms :   94 (79349 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => ( v2_funct_1(X3)
        <=> ! [X4,X5] :
              ( ( r2_hidden(X4,X1)
                & r2_hidden(X5,X1)
                & k1_funct_1(X3,X4) = k1_funct_1(X3,X5) )
             => X4 = X5 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v2_funct_1(X3)
          <=> ! [X4,X5] :
                ( ( r2_hidden(X4,X1)
                  & r2_hidden(X5,X1)
                  & k1_funct_1(X3,X4) = k1_funct_1(X3,X5) )
               => X4 = X5 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_funct_2])).

fof(c_0_6,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v1_funct_2(X19,X17,X18)
        | X17 = k1_relset_1(X17,X18,X19)
        | X18 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X17 != k1_relset_1(X17,X18,X19)
        | v1_funct_2(X19,X17,X18)
        | X18 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_2(X19,X17,X18)
        | X17 = k1_relset_1(X17,X18,X19)
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X17 != k1_relset_1(X17,X18,X19)
        | v1_funct_2(X19,X17,X18)
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_2(X19,X17,X18)
        | X19 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X19 != k1_xboole_0
        | v1_funct_2(X19,X17,X18)
        | X17 = k1_xboole_0
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_7,negated_conjecture,(
    ! [X25,X26] :
      ( v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk3_0,esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
      & ( esk4_0 != k1_xboole_0
        | esk3_0 = k1_xboole_0 )
      & ( r2_hidden(esk6_0,esk3_0)
        | ~ v2_funct_1(esk5_0) )
      & ( r2_hidden(esk7_0,esk3_0)
        | ~ v2_funct_1(esk5_0) )
      & ( k1_funct_1(esk5_0,esk6_0) = k1_funct_1(esk5_0,esk7_0)
        | ~ v2_funct_1(esk5_0) )
      & ( esk6_0 != esk7_0
        | ~ v2_funct_1(esk5_0) )
      & ( v2_funct_1(esk5_0)
        | ~ r2_hidden(X25,esk3_0)
        | ~ r2_hidden(X26,esk3_0)
        | k1_funct_1(esk5_0,X25) != k1_funct_1(esk5_0,X26)
        | X25 = X26 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_9,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v2_funct_1(X6)
        | ~ r2_hidden(X7,k1_relat_1(X6))
        | ~ r2_hidden(X8,k1_relat_1(X6))
        | k1_funct_1(X6,X7) != k1_funct_1(X6,X8)
        | X7 = X8
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk1_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk2_1(X6),k1_relat_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( k1_funct_1(X6,esk1_1(X6)) = k1_funct_1(X6,esk2_1(X6))
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk1_1(X6) != esk2_1(X6)
        | v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_15,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = X2
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk5_0,esk6_0) = k1_funct_1(esk5_0,esk7_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = esk7_0
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( esk6_0 != esk7_0
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk5_0),esk3_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_32,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( X1 = esk1_1(esk5_0)
    | esk4_0 = k1_xboole_0
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,esk2_1(esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_30]),c_0_20]),c_0_21])]),c_0_31]),c_0_32])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( esk1_1(esk5_0) = esk2_1(esk5_0)
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(esk2_1(esk5_0),esk3_0) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk2_1(esk5_0),esk3_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_37,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( esk1_1(esk5_0) = esk2_1(esk5_0)
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20]),c_0_21])]),c_0_32])).

cnf(c_0_41,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_43,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_40]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_40]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_40]),c_0_42]),c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( esk1_1(esk5_0) = X1
    | v2_funct_1(esk5_0)
    | k1_funct_1(esk5_0,esk2_1(esk5_0)) != k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(esk1_1(esk5_0),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_30]),c_0_20])]),c_0_21])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),k1_xboole_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_47]),c_0_20]),c_0_21])])).

cnf(c_0_50,negated_conjecture,
    ( esk1_1(esk5_0) = X1
    | v2_funct_1(esk5_0)
    | k1_funct_1(esk5_0,esk2_1(esk5_0)) != k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_42]),c_0_42]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),k1_xboole_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_20]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( esk1_1(esk5_0) = esk2_1(esk5_0)
    | v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_52]),c_0_20]),c_0_21])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk7_0,k1_xboole_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_47]),c_0_20]),c_0_21])]),c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk5_0,esk7_0) = k1_funct_1(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk7_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_53])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_59,negated_conjecture,
    ( X1 = esk7_0
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,esk6_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_53])])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]),c_0_60])]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t25_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v2_funct_1(X3)<=>![X4, X5]:(((r2_hidden(X4,X1)&r2_hidden(X5,X1))&k1_funct_1(X3,X4)=k1_funct_1(X3,X5))=>X4=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_2)).
% 0.13/0.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.37  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v2_funct_1(X3)<=>![X4, X5]:(((r2_hidden(X4,X1)&r2_hidden(X5,X1))&k1_funct_1(X3,X4)=k1_funct_1(X3,X5))=>X4=X5))))), inference(assume_negation,[status(cth)],[t25_funct_2])).
% 0.13/0.37  fof(c_0_6, plain, ![X17, X18, X19]:((((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&((~v1_funct_2(X19,X17,X18)|X19=k1_xboole_0|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X19!=k1_xboole_0|v1_funct_2(X19,X17,X18)|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ![X25, X26]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&(((((r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk5_0))&(r2_hidden(esk7_0,esk3_0)|~v2_funct_1(esk5_0)))&(k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk5_0,esk7_0)|~v2_funct_1(esk5_0)))&(esk6_0!=esk7_0|~v2_funct_1(esk5_0)))&(v2_funct_1(esk5_0)|(~r2_hidden(X25,esk3_0)|~r2_hidden(X26,esk3_0)|k1_funct_1(esk5_0,X25)!=k1_funct_1(esk5_0,X26)|X25=X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k1_relset_1(X14,X15,X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.37  cnf(c_0_9, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_12, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  fof(c_0_13, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.37  fof(c_0_14, plain, ![X6, X7, X8]:((~v2_funct_1(X6)|(~r2_hidden(X7,k1_relat_1(X6))|~r2_hidden(X8,k1_relat_1(X6))|k1_funct_1(X6,X7)!=k1_funct_1(X6,X8)|X7=X8)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&((((r2_hidden(esk1_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(r2_hidden(esk2_1(X6),k1_relat_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(k1_funct_1(X6,esk1_1(X6))=k1_funct_1(X6,esk2_1(X6))|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(esk1_1(X6)!=esk2_1(X6)|v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_10])).
% 0.13/0.37  cnf(c_0_17, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_18, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_10])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v2_funct_1(esk5_0)|X1=X2|~r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk3_0)|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (esk4_0=k1_xboole_0|X1=X2|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk5_0,esk7_0)|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk7_0,esk3_0)|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_26, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (esk4_0=k1_xboole_0|X1=esk7_0|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,esk6_0)|~r2_hidden(X1,esk3_0)|~v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (esk6_0!=esk7_0|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_30, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_1(esk5_0),esk3_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_20]), c_0_21])])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (esk4_0=k1_xboole_0|~v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (X1=esk1_1(esk5_0)|esk4_0=k1_xboole_0|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,esk2_1(esk5_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_30]), c_0_20]), c_0_21])]), c_0_31]), c_0_32])).
% 0.13/0.37  cnf(c_0_34, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (esk1_1(esk5_0)=esk2_1(esk5_0)|esk4_0=k1_xboole_0|~r2_hidden(esk2_1(esk5_0),esk3_0)), inference(er,[status(thm)],[c_0_33])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk2_1(esk5_0),esk3_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_19]), c_0_20]), c_0_21])])).
% 0.13/0.37  cnf(c_0_37, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (esk1_1(esk5_0)=esk2_1(esk5_0)|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_20]), c_0_21])]), c_0_32])).
% 0.13/0.37  cnf(c_0_41, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.13/0.37  cnf(c_0_43, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_41])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10, c_0_40]), c_0_42])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_40]), c_0_42])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_40]), c_0_42]), c_0_46])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (esk1_1(esk5_0)=X1|v2_funct_1(esk5_0)|k1_funct_1(esk5_0,esk2_1(esk5_0))!=k1_funct_1(esk5_0,X1)|~r2_hidden(esk1_1(esk5_0),esk3_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_30]), c_0_20])]), c_0_21])])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_1(esk5_0),k1_xboole_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_47]), c_0_20]), c_0_21])])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (esk1_1(esk5_0)=X1|v2_funct_1(esk5_0)|k1_funct_1(esk5_0,esk2_1(esk5_0))!=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_42]), c_0_42]), c_0_49])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (r2_hidden(esk2_1(esk5_0),k1_xboole_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_20]), c_0_21])])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (esk1_1(esk5_0)=esk2_1(esk5_0)|v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_50]), c_0_51])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_52]), c_0_20]), c_0_21])])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, (r2_hidden(esk7_0,k1_xboole_0)|~v2_funct_1(esk5_0)), inference(rw,[status(thm)],[c_0_25, c_0_42])).
% 0.13/0.37  cnf(c_0_55, negated_conjecture, (X1=X2|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)|~r2_hidden(X2,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_47]), c_0_20]), c_0_21])]), c_0_53])])).
% 0.13/0.37  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk5_0,esk7_0)=k1_funct_1(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_53])])).
% 0.13/0.37  cnf(c_0_57, negated_conjecture, (r2_hidden(esk7_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_53])])).
% 0.13/0.37  cnf(c_0_58, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)|~v2_funct_1(esk5_0)), inference(rw,[status(thm)],[c_0_28, c_0_42])).
% 0.13/0.37  cnf(c_0_59, negated_conjecture, (X1=esk7_0|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,esk6_0)|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.13/0.37  cnf(c_0_60, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_53])])).
% 0.13/0.37  cnf(c_0_61, negated_conjecture, (esk7_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_53])])).
% 0.13/0.37  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_59]), c_0_60])]), c_0_61]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 63
% 0.13/0.37  # Proof object clause steps            : 52
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 45
% 0.13/0.37  # Proof object clause conjectures      : 42
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 18
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 22
% 0.13/0.37  # Proof object simplifying inferences  : 74
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 22
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 22
% 0.13/0.37  # Processed clauses                    : 60
% 0.13/0.37  # ...of these trivial                  : 1
% 0.13/0.37  # ...subsumed                          : 1
% 0.13/0.37  # ...remaining for further processing  : 58
% 0.13/0.37  # Other redundant clauses eliminated   : 5
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 2
% 0.13/0.37  # Backward-rewritten                   : 24
% 0.13/0.37  # Generated clauses                    : 51
% 0.13/0.37  # ...of the previous two non-trivial   : 48
% 0.13/0.37  # Contextual simplify-reflections      : 10
% 0.13/0.37  # Paramodulations                      : 40
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 12
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 28
% 0.13/0.37  #    Positive orientable unit clauses  : 12
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 15
% 0.13/0.37  # Current number of unprocessed clauses: 5
% 0.13/0.37  # ...number of literals in the above   : 26
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 26
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 232
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 87
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.13/0.37  # Unit Clause-clause subsumption calls : 23
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 4
% 0.13/0.37  # BW rewrite match successes           : 4
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2598
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
