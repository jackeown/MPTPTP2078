%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 (7705 expanded)
%              Number of clauses        :   58 (2855 expanded)
%              Number of leaves         :    7 (1935 expanded)
%              Depth                    :   19
%              Number of atoms          :  280 (49844 expanded)
%              Number of equality atoms :   71 (13389 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_funct_2])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_relat_1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_9,negated_conjecture,(
    ! [X26,X27] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk3_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
      & ( r2_hidden(esk5_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( r2_hidden(esk6_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
        | ~ v2_funct_1(esk4_0) )
      & ( esk5_0 != esk6_0
        | ~ v2_funct_1(esk4_0) )
      & ( v2_funct_1(esk4_0)
        | ~ r2_hidden(X26,esk3_0)
        | ~ r2_hidden(X27,esk3_0)
        | k1_funct_1(esk4_0,X26) != k1_funct_1(esk4_0,X27)
        | X26 = X27 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X7,X8] : v1_relat_1(k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_11,plain,(
    ! [X14,X15] :
      ( ( X14 = k1_funct_1(k2_funct_1(X15),k1_funct_1(X15,X14))
        | ~ v2_funct_1(X15)
        | ~ r2_hidden(X14,k1_relat_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X14 = k1_funct_1(k5_relat_1(X15,k2_funct_1(X15)),X14)
        | ~ v2_funct_1(X15)
        | ~ r2_hidden(X14,k1_relat_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_12,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X21 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != k1_xboole_0
        | v1_funct_2(X21,X19,X20)
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0)) = esk6_0
    | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( esk5_0 != esk6_0
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_funct_1(X9)
        | ~ r2_hidden(X10,k1_relat_1(X9))
        | ~ r2_hidden(X11,k1_relat_1(X9))
        | k1_funct_1(X9,X10) != k1_funct_1(X9,X11)
        | X10 = X11
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk1_1(X9),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk2_1(X9),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( k1_funct_1(X9,esk1_1(X9)) = k1_funct_1(X9,esk2_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk1_1(X9) != esk2_1(X9)
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_28,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | ~ v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23]),c_0_19]),c_0_20])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_13]),c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k1_relat_1(esk4_0))
    | v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_19]),c_0_20])])).

cnf(c_0_38,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_1(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_19]),c_0_20])]),c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k1_xboole_0)
    | v2_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)
    | r2_hidden(esk1_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk1_1(esk4_0),esk3_0)
    | v2_funct_1(esk4_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk3_0)
    | r2_hidden(esk2_1(esk4_0),k1_xboole_0)
    | v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0))
    | v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_19]),c_0_20])])).

cnf(c_0_47,negated_conjecture,
    ( X1 = esk2_1(esk4_0)
    | r2_hidden(esk1_1(esk4_0),esk3_0)
    | v2_funct_1(esk4_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk2_1(esk4_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),k1_xboole_0)
    | v2_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_50,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( X1 = esk2_1(esk4_0)
    | r2_hidden(esk1_1(esk4_0),esk3_0)
    | v2_funct_1(esk4_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk1_1(esk4_0))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_19]),c_0_20])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk3_0)
    | r2_hidden(esk1_1(esk4_0),k1_xboole_0)
    | v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | esk2_1(esk4_0) != esk1_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_19]),c_0_20])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_0),esk3_0)
    | v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk2_1(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_19]),c_0_20])]),c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( X1 = esk1_1(esk4_0)
    | v2_funct_1(esk4_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk1_1(esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)
    | r2_hidden(esk2_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | ~ r2_hidden(esk2_1(esk4_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_19]),c_0_20])]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),esk3_0)
    | r2_hidden(esk2_1(esk4_0),k1_xboole_0)
    | v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_57]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ r2_hidden(esk5_0,k1_xboole_0)
    | ~ r2_hidden(esk6_0,k1_xboole_0)
    | ~ v2_funct_1(esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_0,k1_xboole_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_36])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),k1_xboole_0)
    | v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ v2_funct_1(esk4_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_64]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_36])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_66])])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:47:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.20/0.50  # and selection function PSelectUnlessUniqMaxPos.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.028 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t77_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 0.20/0.50  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.50  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.50  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 0.20/0.50  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.50  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.50  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.20/0.50  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t77_funct_2])).
% 0.20/0.50  fof(c_0_8, plain, ![X5, X6]:(~v1_relat_1(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_relat_1(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.50  fof(c_0_9, negated_conjecture, ![X26, X27]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(((((r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0))&(r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)))&(k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)))&(esk5_0!=esk6_0|~v2_funct_1(esk4_0)))&(v2_funct_1(esk4_0)|(~r2_hidden(X26,esk3_0)|~r2_hidden(X27,esk3_0)|k1_funct_1(esk4_0,X26)!=k1_funct_1(esk4_0,X27)|X26=X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).
% 0.20/0.50  fof(c_0_10, plain, ![X7, X8]:v1_relat_1(k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.50  fof(c_0_11, plain, ![X14, X15]:((X14=k1_funct_1(k2_funct_1(X15),k1_funct_1(X15,X14))|(~v2_funct_1(X15)|~r2_hidden(X14,k1_relat_1(X15)))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(X14=k1_funct_1(k5_relat_1(X15,k2_funct_1(X15)),X14)|(~v2_funct_1(X15)|~r2_hidden(X14,k1_relat_1(X15)))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.20/0.50  cnf(c_0_12, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.50  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_14, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.50  fof(c_0_15, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.50  fof(c_0_16, plain, ![X19, X20, X21]:((((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))&((~v1_funct_2(X21,X19,X20)|X21=k1_xboole_0|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X21!=k1_xboole_0|v1_funct_2(X21,X19,X20)|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.50  cnf(c_0_17, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.50  cnf(c_0_18, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.20/0.50  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_23, negated_conjecture, (k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))=esk6_0|~r2_hidden(esk6_0,k1_relat_1(esk4_0))|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.50  cnf(c_0_24, negated_conjecture, (esk5_0!=esk6_0|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_25, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.50  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  fof(c_0_27, plain, ![X9, X10, X11]:((~v2_funct_1(X9)|(~r2_hidden(X10,k1_relat_1(X9))|~r2_hidden(X11,k1_relat_1(X9))|k1_funct_1(X9,X10)!=k1_funct_1(X9,X11)|X10=X11)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&((((r2_hidden(esk1_1(X9),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(r2_hidden(esk2_1(X9),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(k1_funct_1(X9,esk1_1(X9))=k1_funct_1(X9,esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(esk1_1(X9)!=esk2_1(X9)|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.20/0.50  cnf(c_0_28, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk5_0,k1_relat_1(esk4_0))|~r2_hidden(esk6_0,k1_relat_1(esk4_0))|~v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_23]), c_0_19]), c_0_20])]), c_0_24])).
% 0.20/0.50  cnf(c_0_30, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_13]), c_0_26])])).
% 0.20/0.50  cnf(c_0_31, negated_conjecture, (r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_33, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_34, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_28])).
% 0.20/0.50  cnf(c_0_35, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_36, negated_conjecture, (esk3_0=k1_xboole_0|~v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.50  cnf(c_0_37, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k1_relat_1(esk4_0))|v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_19]), c_0_20])])).
% 0.20/0.50  cnf(c_0_38, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_21, c_0_34])).
% 0.20/0.50  cnf(c_0_39, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_1(esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_30]), c_0_19]), c_0_20])]), c_0_36])).
% 0.20/0.50  cnf(c_0_40, negated_conjecture, (v2_funct_1(esk4_0)|X1=X2|~r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk3_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.50  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k1_xboole_0)|v2_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.50  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_13, c_0_39])).
% 0.20/0.50  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)|r2_hidden(esk1_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_39])).
% 0.20/0.50  cnf(c_0_44, negated_conjecture, (X1=X2|r2_hidden(esk1_1(esk4_0),esk3_0)|v2_funct_1(esk4_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)|~r2_hidden(X2,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.20/0.50  cnf(c_0_45, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk3_0)|r2_hidden(esk2_1(esk4_0),k1_xboole_0)|v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.20/0.50  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0))|v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_19]), c_0_20])])).
% 0.20/0.50  cnf(c_0_47, negated_conjecture, (X1=esk2_1(esk4_0)|r2_hidden(esk1_1(esk4_0),esk3_0)|v2_funct_1(esk4_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk2_1(esk4_0))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.50  cnf(c_0_48, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_1(esk4_0),k1_xboole_0)|v2_funct_1(esk4_0)|~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_46, c_0_38])).
% 0.20/0.50  cnf(c_0_50, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (X1=esk2_1(esk4_0)|r2_hidden(esk1_1(esk4_0),esk3_0)|v2_funct_1(esk4_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk1_1(esk4_0))|~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_19]), c_0_20])])).
% 0.20/0.50  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk3_0)|r2_hidden(esk1_1(esk4_0),k1_xboole_0)|v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_42]), c_0_43])).
% 0.20/0.50  cnf(c_0_53, negated_conjecture, (v2_funct_1(esk4_0)|esk2_1(esk4_0)!=esk1_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_19]), c_0_20])])).
% 0.20/0.50  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_1(esk4_0),esk3_0)|v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_51]), c_0_52]), c_0_53])).
% 0.20/0.50  cnf(c_0_55, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk2_1(esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_19]), c_0_20])]), c_0_36])).
% 0.20/0.50  cnf(c_0_56, negated_conjecture, (X1=esk1_1(esk4_0)|v2_funct_1(esk4_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk1_1(esk4_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_40, c_0_54])).
% 0.20/0.50  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_13, c_0_55])).
% 0.20/0.50  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)|r2_hidden(esk2_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_55])).
% 0.20/0.50  cnf(c_0_59, negated_conjecture, (v2_funct_1(esk4_0)|~r2_hidden(esk2_1(esk4_0),esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_19]), c_0_20])]), c_0_53])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_1(esk4_0),esk3_0)|r2_hidden(esk2_1(esk4_0),k1_xboole_0)|v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_57]), c_0_58])).
% 0.20/0.50  cnf(c_0_61, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,X1)|~r2_hidden(esk5_0,k1_xboole_0)|~r2_hidden(esk6_0,k1_xboole_0)|~v2_funct_1(esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.20/0.50  cnf(c_0_62, negated_conjecture, (r2_hidden(esk5_0,k1_xboole_0)|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_36])).
% 0.20/0.50  cnf(c_0_63, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 0.20/0.50  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_1(esk4_0),k1_xboole_0)|v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.50  cnf(c_0_65, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,X1)|~v2_funct_1(esk4_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.20/0.50  cnf(c_0_66, negated_conjecture, (v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_55]), c_0_64]), c_0_59])).
% 0.20/0.50  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_36])).
% 0.20/0.50  cnf(c_0_68, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.20/0.50  cnf(c_0_69, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.20/0.50  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_66])])).
% 0.20/0.50  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_66])])).
% 0.20/0.50  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 73
% 0.20/0.50  # Proof object clause steps            : 58
% 0.20/0.50  # Proof object formula steps           : 15
% 0.20/0.50  # Proof object conjectures             : 48
% 0.20/0.50  # Proof object clause conjectures      : 45
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 18
% 0.20/0.50  # Proof object initial formulas used   : 7
% 0.20/0.50  # Proof object generating inferences   : 36
% 0.20/0.50  # Proof object simplifying inferences  : 51
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 7
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 24
% 0.20/0.50  # Removed in clause preprocessing      : 0
% 0.20/0.50  # Initial clauses in saturation        : 24
% 0.20/0.50  # Processed clauses                    : 524
% 0.20/0.50  # ...of these trivial                  : 3
% 0.20/0.50  # ...subsumed                          : 185
% 0.20/0.50  # ...remaining for further processing  : 336
% 0.20/0.50  # Other redundant clauses eliminated   : 86
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 45
% 0.20/0.50  # Backward-rewritten                   : 147
% 0.20/0.50  # Generated clauses                    : 5333
% 0.20/0.50  # ...of the previous two non-trivial   : 5215
% 0.20/0.50  # Contextual simplify-reflections      : 18
% 0.20/0.50  # Paramodulations                      : 5205
% 0.20/0.50  # Factorizations                       : 40
% 0.20/0.50  # Equation resolutions                 : 89
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 116
% 0.20/0.50  #    Positive orientable unit clauses  : 10
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 1
% 0.20/0.50  #    Non-unit-clauses                  : 105
% 0.20/0.50  # Current number of unprocessed clauses: 4735
% 0.20/0.50  # ...number of literals in the above   : 35858
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 216
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 16521
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 2483
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 245
% 0.20/0.50  # Unit Clause-clause subsumption calls : 415
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 11
% 0.20/0.50  # BW rewrite match successes           : 4
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 136095
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.148 s
% 0.20/0.51  # System time              : 0.010 s
% 0.20/0.51  # Total time               : 0.158 s
% 0.20/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
