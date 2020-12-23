%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:02 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (16625 expanded)
%              Number of clauses        :   52 (6104 expanded)
%              Number of leaves         :    6 (4071 expanded)
%              Depth                    :   23
%              Number of atoms          :  247 (129198 expanded)
%              Number of equality atoms :   94 (46811 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X20 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X20 != k1_xboole_0
        | v1_funct_2(X20,X18,X19)
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_8,negated_conjecture,(
    ! [X26,X27] :
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
        | ~ r2_hidden(X26,esk3_0)
        | ~ r2_hidden(X27,esk3_0)
        | k1_funct_1(esk5_0,X26) != k1_funct_1(esk5_0,X27)
        | X26 = X27 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

fof(c_0_9,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_relset_1(X15,X16,X17) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_10,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,plain,(
    ! [X8,X9] : v1_relat_1(k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_funct_1(X10)
        | ~ r2_hidden(X11,k1_relat_1(X10))
        | ~ r2_hidden(X12,k1_relat_1(X10))
        | k1_funct_1(X10,X11) != k1_funct_1(X10,X12)
        | X11 = X12
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk1_1(X10),k1_relat_1(X10))
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk2_1(X10),k1_relat_1(X10))
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( k1_funct_1(X10,esk1_1(X10)) = k1_funct_1(X10,esk2_1(X10))
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk1_1(X10) != esk2_1(X10)
        | v2_funct_1(X10)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_17,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_18,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = X2
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk5_0,esk6_0) = k1_funct_1(esk5_0,esk7_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk7_0,esk3_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = esk7_0
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,esk6_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( esk6_0 != esk7_0
    | ~ v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk5_0),esk3_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( X1 = esk1_1(esk5_0)
    | esk4_0 = k1_xboole_0
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,esk2_1(esk5_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_33]),c_0_23]),c_0_24])]),c_0_34]),c_0_35])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( esk1_1(esk5_0) = esk2_1(esk5_0)
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(esk2_1(esk5_0),esk3_0) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk2_1(esk5_0),esk3_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_40,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( esk1_1(esk5_0) = esk2_1(esk5_0)
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_23]),c_0_24])]),c_0_35])).

cnf(c_0_44,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_46,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_43]),c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_43]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_43]),c_0_45]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_50]),c_0_23]),c_0_24])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk7_0,k1_xboole_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( X1 = esk7_0
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,esk6_0)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0)
    | ~ v2_funct_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( esk1_1(esk5_0) = X1
    | v2_funct_1(esk5_0)
    | k1_funct_1(esk5_0,esk2_1(esk5_0)) != k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(esk1_1(esk5_0),esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_33]),c_0_23])]),c_0_24])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),k1_xboole_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_50]),c_0_23]),c_0_24])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]),c_0_54]),c_0_32])).

cnf(c_0_58,negated_conjecture,
    ( esk1_1(esk5_0) = X1
    | v2_funct_1(esk5_0)
    | k1_funct_1(esk5_0,esk2_1(esk5_0)) != k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(esk1_1(esk5_0),k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_45]),c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),k1_xboole_0)
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_50]),c_0_23]),c_0_24])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_1(esk5_0) = X1
    | k1_funct_1(esk5_0,esk2_1(esk5_0)) != k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[c_0_60,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( esk1_1(esk5_0) = esk2_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]),c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_63]),c_0_23]),c_0_24])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:00:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.20/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.039 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t25_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v2_funct_1(X3)<=>![X4, X5]:(((r2_hidden(X4,X1)&r2_hidden(X5,X1))&k1_funct_1(X3,X4)=k1_funct_1(X3,X5))=>X4=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_2)).
% 0.20/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.38  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.20/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v2_funct_1(X3)<=>![X4, X5]:(((r2_hidden(X4,X1)&r2_hidden(X5,X1))&k1_funct_1(X3,X4)=k1_funct_1(X3,X5))=>X4=X5))))), inference(assume_negation,[status(cth)],[t25_funct_2])).
% 0.20/0.38  fof(c_0_7, plain, ![X18, X19, X20]:((((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))&((~v1_funct_2(X20,X18,X19)|X20=k1_xboole_0|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X20!=k1_xboole_0|v1_funct_2(X20,X18,X19)|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.38  fof(c_0_8, negated_conjecture, ![X26, X27]:(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&(((((r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk5_0))&(r2_hidden(esk7_0,esk3_0)|~v2_funct_1(esk5_0)))&(k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk5_0,esk7_0)|~v2_funct_1(esk5_0)))&(esk6_0!=esk7_0|~v2_funct_1(esk5_0)))&(v2_funct_1(esk5_0)|(~r2_hidden(X26,esk3_0)|~r2_hidden(X27,esk3_0)|k1_funct_1(esk5_0,X26)!=k1_funct_1(esk5_0,X27)|X26=X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k1_relset_1(X15,X16,X17)=k1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.38  cnf(c_0_10, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_13, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_14, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X8, X9]:v1_relat_1(k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.38  fof(c_0_16, plain, ![X10, X11, X12]:((~v2_funct_1(X10)|(~r2_hidden(X11,k1_relat_1(X10))|~r2_hidden(X12,k1_relat_1(X10))|k1_funct_1(X10,X11)!=k1_funct_1(X10,X12)|X11=X12)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&((((r2_hidden(esk1_1(X10),k1_relat_1(X10))|v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(r2_hidden(esk2_1(X10),k1_relat_1(X10))|v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(k1_funct_1(X10,esk1_1(X10))=k1_funct_1(X10,esk2_1(X10))|v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(esk1_1(X10)!=esk2_1(X10)|v2_funct_1(X10)|(~v1_relat_1(X10)|~v1_funct_1(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.20/0.38  cnf(c_0_19, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_21, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_11]), c_0_20])])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (v2_funct_1(esk5_0)|X1=X2|~r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk3_0)|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (esk4_0=k1_xboole_0|X1=X2|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk5_0,esk7_0)|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk7_0,esk3_0)|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_29, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (esk4_0=k1_xboole_0|X1=esk7_0|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,esk6_0)|~r2_hidden(X1,esk3_0)|~v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (esk6_0!=esk7_0|~v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_33, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_1(esk5_0),esk3_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_22]), c_0_23]), c_0_24])])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (esk4_0=k1_xboole_0|~v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (X1=esk1_1(esk5_0)|esk4_0=k1_xboole_0|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,esk2_1(esk5_0))|~r2_hidden(X1,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_33]), c_0_23]), c_0_24])]), c_0_34]), c_0_35])).
% 0.20/0.38  cnf(c_0_37, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (esk1_1(esk5_0)=esk2_1(esk5_0)|esk4_0=k1_xboole_0|~r2_hidden(esk2_1(esk5_0),esk3_0)), inference(er,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk2_1(esk5_0),esk3_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_22]), c_0_23]), c_0_24])])).
% 0.20/0.38  cnf(c_0_40, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (esk1_1(esk5_0)=esk2_1(esk5_0)|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_35])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_23]), c_0_24])]), c_0_35])).
% 0.20/0.38  cnf(c_0_44, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.20/0.38  cnf(c_0_46, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_43]), c_0_45])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_43]), c_0_45])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_43]), c_0_45]), c_0_49])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (X1=X2|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)|~r2_hidden(X2,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)|~v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_50]), c_0_23]), c_0_24])])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (r2_hidden(esk7_0,k1_xboole_0)|~v2_funct_1(esk5_0)), inference(rw,[status(thm)],[c_0_28, c_0_45])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (X1=esk7_0|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,esk6_0)|~r2_hidden(X1,k1_xboole_0)|~v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_27]), c_0_52])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)|~v2_funct_1(esk5_0)), inference(rw,[status(thm)],[c_0_31, c_0_45])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (esk1_1(esk5_0)=X1|v2_funct_1(esk5_0)|k1_funct_1(esk5_0,esk2_1(esk5_0))!=k1_funct_1(esk5_0,X1)|~r2_hidden(esk1_1(esk5_0),esk3_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_33]), c_0_23])]), c_0_24])])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_1(esk5_0),k1_xboole_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_50]), c_0_23]), c_0_24])])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (~v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_53]), c_0_54]), c_0_32])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (esk1_1(esk5_0)=X1|v2_funct_1(esk5_0)|k1_funct_1(esk5_0,esk2_1(esk5_0))!=k1_funct_1(esk5_0,X1)|~r2_hidden(esk1_1(esk5_0),k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_45]), c_0_45])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (r2_hidden(esk1_1(esk5_0),k1_xboole_0)), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_1(esk5_0),k1_xboole_0)|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_50]), c_0_23]), c_0_24])])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (esk1_1(esk5_0)=X1|k1_funct_1(esk5_0,esk2_1(esk5_0))!=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])]), c_0_57])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_1(esk5_0),k1_xboole_0)), inference(sr,[status(thm)],[c_0_60, c_0_57])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (esk1_1(esk5_0)=esk2_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_61]), c_0_62])])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_63]), c_0_23]), c_0_24])]), c_0_57]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 65
% 0.20/0.38  # Proof object clause steps            : 52
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 44
% 0.20/0.38  # Proof object clause conjectures      : 41
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 19
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 22
% 0.20/0.38  # Proof object simplifying inferences  : 70
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 23
% 0.20/0.38  # Processed clauses                    : 62
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 2
% 0.20/0.38  # ...remaining for further processing  : 59
% 0.20/0.38  # Other redundant clauses eliminated   : 5
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 3
% 0.20/0.38  # Backward-rewritten                   : 19
% 0.20/0.38  # Generated clauses                    : 58
% 0.20/0.38  # ...of the previous two non-trivial   : 51
% 0.20/0.38  # Contextual simplify-reflections      : 11
% 0.20/0.38  # Paramodulations                      : 44
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 13
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 31
% 0.20/0.38  #    Positive orientable unit clauses  : 11
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 19
% 0.20/0.38  # Current number of unprocessed clauses: 9
% 0.20/0.38  # ...number of literals in the above   : 43
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 24
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 224
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 84
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 15
% 0.20/0.38  # Unit Clause-clause subsumption calls : 25
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 5
% 0.20/0.38  # BW rewrite match successes           : 5
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2776
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.042 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.046 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
