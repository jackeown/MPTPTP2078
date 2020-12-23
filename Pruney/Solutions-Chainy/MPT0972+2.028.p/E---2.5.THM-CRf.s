%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 565 expanded)
%              Number of clauses        :   46 ( 224 expanded)
%              Number of leaves         :   10 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 (3157 expanded)
%              Number of equality atoms :   95 ( 789 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( r2_hidden(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_2])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X36] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk2_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( ~ r2_hidden(X36,esk2_0)
        | k1_funct_1(esk4_0,X36) = k1_funct_1(esk5_0,X36) )
      & ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X30 = k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X29 = k1_relset_1(X29,X30,X31)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X29 != k1_relset_1(X29,X30,X31)
        | v1_funct_2(X31,X29,X30)
        | X29 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( ~ v1_funct_2(X31,X29,X30)
        | X31 = k1_xboole_0
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X31 != k1_xboole_0
        | v1_funct_2(X31,X29,X30)
        | X29 = k1_xboole_0
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_14,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,plain,(
    ! [X16,X17] :
      ( ( r2_hidden(esk1_2(X16,X17),k1_relat_1(X16))
        | k1_relat_1(X16) != k1_relat_1(X17)
        | X16 = X17
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_funct_1(X16,esk1_2(X16,X17)) != k1_funct_1(X17,esk1_2(X16,X17))
        | k1_relat_1(X16) != k1_relat_1(X17)
        | X16 = X17
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( X1 = esk5_0
    | r2_hidden(esk1_2(X1,esk5_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_17]),c_0_27])]),c_0_28])).

fof(c_0_34,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = esk5_0
    | r2_hidden(esk1_2(esk4_0,esk5_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])]),c_0_33])).

fof(c_0_38,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk5_0
    | k1_funct_1(X1,esk1_2(X1,esk5_0)) != k1_funct_1(esk5_0,esk1_2(X1,esk5_0))
    | k1_relat_1(X1) != k1_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_23]),c_0_24])])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0)) = k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0))
    | esk4_0 = esk5_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_42,plain,(
    ! [X8,X9] :
      ( ( k2_zfmisc_1(X8,X9) != k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_43,plain,(
    ! [X10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_44,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ r2_relset_1(X25,X26,X27,X28)
        | X27 = X28
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X27 != X28
        | r2_relset_1(X25,X26,X27,X28)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = esk5_0
    | k1_relat_1(esk4_0) != k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31]),c_0_32])])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 = esk5_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_30]),c_0_33])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_49])).

cnf(c_0_55,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_53]),c_0_54])])).

cnf(c_0_58,negated_conjecture,
    ( r2_relset_1(esk2_0,esk3_0,esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_52,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_relset_1(esk2_0,esk3_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_53]),c_0_53]),c_0_54])])).

cnf(c_0_65,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.20/0.36  # and selection function SelectComplexG.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.014 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t18_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 0.20/0.36  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.36  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.36  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.36  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.20/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.36  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.36  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.36  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.36  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t18_funct_2])).
% 0.20/0.36  fof(c_0_11, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.36  fof(c_0_12, negated_conjecture, ![X36]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((~r2_hidden(X36,esk2_0)|k1_funct_1(esk4_0,X36)=k1_funct_1(esk5_0,X36))&~r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.20/0.36  fof(c_0_13, plain, ![X29, X30, X31]:((((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X30=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))&((~v1_funct_2(X31,X29,X30)|X29=k1_relset_1(X29,X30,X31)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X29!=k1_relset_1(X29,X30,X31)|v1_funct_2(X31,X29,X30)|X29!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))))&((~v1_funct_2(X31,X29,X30)|X31=k1_xboole_0|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(X31!=k1_xboole_0|v1_funct_2(X31,X29,X30)|X29=k1_xboole_0|X30!=k1_xboole_0|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.36  fof(c_0_14, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k1_relset_1(X22,X23,X24)=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.36  fof(c_0_15, plain, ![X16, X17]:((r2_hidden(esk1_2(X16,X17),k1_relat_1(X16))|k1_relat_1(X16)!=k1_relat_1(X17)|X16=X17|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(k1_funct_1(X16,esk1_2(X16,X17))!=k1_funct_1(X17,esk1_2(X16,X17))|k1_relat_1(X16)!=k1_relat_1(X17)|X16=X17|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.20/0.36  cnf(c_0_16, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.36  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_18, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.36  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.36  cnf(c_0_22, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.36  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.36  cnf(c_0_25, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.20/0.36  cnf(c_0_26, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.20/0.36  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_28, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_17])).
% 0.20/0.36  cnf(c_0_29, negated_conjecture, (X1=esk5_0|r2_hidden(esk1_2(X1,esk5_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.20/0.36  cnf(c_0_30, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.36  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_19])).
% 0.20/0.36  cnf(c_0_33, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_17]), c_0_27])]), c_0_28])).
% 0.20/0.36  fof(c_0_34, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.36  cnf(c_0_35, plain, (X1=X2|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.36  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_37, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=esk5_0|r2_hidden(esk1_2(esk4_0,esk5_0),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])]), c_0_33])).
% 0.20/0.36  fof(c_0_38, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.36  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.36  cnf(c_0_40, negated_conjecture, (X1=esk5_0|k1_funct_1(X1,esk1_2(X1,esk5_0))!=k1_funct_1(esk5_0,esk1_2(X1,esk5_0))|k1_relat_1(X1)!=k1_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_23]), c_0_24])])).
% 0.20/0.36  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0))=k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0))|esk4_0=esk5_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.36  fof(c_0_42, plain, ![X8, X9]:((k2_zfmisc_1(X8,X9)!=k1_xboole_0|(X8=k1_xboole_0|X9=k1_xboole_0))&((X8!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0)&(X9!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.36  fof(c_0_43, plain, ![X10]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.36  fof(c_0_44, plain, ![X25, X26, X27, X28]:((~r2_relset_1(X25,X26,X27,X28)|X27=X28|(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&(X27!=X28|r2_relset_1(X25,X26,X27,X28)|(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.36  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.36  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_17])).
% 0.20/0.36  cnf(c_0_47, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=esk5_0|k1_relat_1(esk4_0)!=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31]), c_0_32])])).
% 0.20/0.36  cnf(c_0_48, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.36  cnf(c_0_49, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.36  cnf(c_0_50, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.36  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk5_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.36  cnf(c_0_52, negated_conjecture, (esk4_0=esk5_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_30]), c_0_33])).
% 0.20/0.36  cnf(c_0_53, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_48])).
% 0.20/0.36  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_49])).
% 0.20/0.36  cnf(c_0_55, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.36  cnf(c_0_56, negated_conjecture, (~r2_relset_1(esk2_0,esk3_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.36  cnf(c_0_57, negated_conjecture, (esk4_0=esk5_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_53]), c_0_54])])).
% 0.20/0.36  cnf(c_0_58, negated_conjecture, (r2_relset_1(esk2_0,esk3_0,esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_55, c_0_17])).
% 0.20/0.36  cnf(c_0_59, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_19])).
% 0.20/0.36  cnf(c_0_60, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.20/0.36  cnf(c_0_61, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_59])).
% 0.20/0.36  cnf(c_0_62, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_52, c_0_60])).
% 0.20/0.36  cnf(c_0_63, negated_conjecture, (~r2_relset_1(esk2_0,esk3_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_56, c_0_60])).
% 0.20/0.36  cnf(c_0_64, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_53]), c_0_53]), c_0_54])])).
% 0.20/0.36  cnf(c_0_65, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 0.20/0.36  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_65])]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 67
% 0.20/0.36  # Proof object clause steps            : 46
% 0.20/0.36  # Proof object formula steps           : 21
% 0.20/0.36  # Proof object conjectures             : 35
% 0.20/0.36  # Proof object clause conjectures      : 32
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 18
% 0.20/0.36  # Proof object initial formulas used   : 10
% 0.20/0.36  # Proof object generating inferences   : 23
% 0.20/0.36  # Proof object simplifying inferences  : 34
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 11
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 30
% 0.20/0.36  # Removed in clause preprocessing      : 0
% 0.20/0.36  # Initial clauses in saturation        : 30
% 0.20/0.36  # Processed clauses                    : 147
% 0.20/0.36  # ...of these trivial                  : 0
% 0.20/0.36  # ...subsumed                          : 11
% 0.20/0.36  # ...remaining for further processing  : 136
% 0.20/0.36  # Other redundant clauses eliminated   : 11
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 4
% 0.20/0.36  # Backward-rewritten                   : 40
% 0.20/0.36  # Generated clauses                    : 160
% 0.20/0.36  # ...of the previous two non-trivial   : 141
% 0.20/0.36  # Contextual simplify-reflections      : 2
% 0.20/0.36  # Paramodulations                      : 148
% 0.20/0.36  # Factorizations                       : 0
% 0.20/0.36  # Equation resolutions                 : 13
% 0.20/0.36  # Propositional unsat checks           : 0
% 0.20/0.36  #    Propositional check models        : 0
% 0.20/0.36  #    Propositional check unsatisfiable : 0
% 0.20/0.36  #    Propositional clauses             : 0
% 0.20/0.36  #    Propositional clauses after purity: 0
% 0.20/0.36  #    Propositional unsat core size     : 0
% 0.20/0.36  #    Propositional preprocessing time  : 0.000
% 0.20/0.36  #    Propositional encoding time       : 0.000
% 0.20/0.36  #    Propositional solver time         : 0.000
% 0.20/0.36  #    Success case prop preproc time    : 0.000
% 0.20/0.36  #    Success case prop encoding time   : 0.000
% 0.20/0.36  #    Success case prop solver time     : 0.000
% 0.20/0.36  # Current number of processed clauses  : 53
% 0.20/0.36  #    Positive orientable unit clauses  : 15
% 0.20/0.36  #    Positive unorientable unit clauses: 0
% 0.20/0.36  #    Negative unit clauses             : 0
% 0.20/0.36  #    Non-unit-clauses                  : 38
% 0.20/0.36  # Current number of unprocessed clauses: 50
% 0.20/0.36  # ...number of literals in the above   : 138
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 73
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 693
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 500
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 16
% 0.20/0.36  # Unit Clause-clause subsumption calls : 97
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 58
% 0.20/0.36  # BW rewrite match successes           : 3
% 0.20/0.36  # Condensation attempts                : 0
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 4253
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.017 s
% 0.20/0.36  # System time              : 0.004 s
% 0.20/0.36  # Total time               : 0.021 s
% 0.20/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
