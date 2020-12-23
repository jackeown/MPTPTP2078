%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:03 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 (21803 expanded)
%              Number of clauses        :   57 (8340 expanded)
%              Number of leaves         :   10 (5455 expanded)
%              Depth                    :   23
%              Number of atoms          :  271 (129962 expanded)
%              Number of equality atoms :   77 (34886 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t145_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( X2 = k1_xboole_0
             => X1 = k1_xboole_0 )
           => ( r1_partfun1(X3,X4)
            <=> ! [X5] :
                  ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

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

fof(t132_partfun1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
           => ( r1_partfun1(X1,X2)
            <=> ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ( X2 = k1_xboole_0
               => X1 = k1_xboole_0 )
             => ( r1_partfun1(X3,X4)
              <=> ! [X5] :
                    ( r2_hidden(X5,k1_relset_1(X1,X2,X3))
                   => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t145_funct_2])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,negated_conjecture,(
    ! [X33] :
      ( v1_funct_1(esk4_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,esk2_0,esk3_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
      & ( esk3_0 != k1_xboole_0
        | esk2_0 = k1_xboole_0 )
      & ( r2_hidden(esk6_0,k1_relset_1(esk2_0,esk3_0,esk4_0))
        | ~ r1_partfun1(esk4_0,esk5_0) )
      & ( k1_funct_1(esk4_0,esk6_0) != k1_funct_1(esk5_0,esk6_0)
        | ~ r1_partfun1(esk4_0,esk5_0) )
      & ( r1_partfun1(esk4_0,esk5_0)
        | ~ r2_hidden(X33,k1_relset_1(esk2_0,esk3_0,esk4_0))
        | k1_funct_1(esk4_0,X33) = k1_funct_1(esk5_0,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_14,plain,(
    ! [X24,X25,X26] :
      ( ( ~ r1_partfun1(X24,X25)
        | ~ r2_hidden(X26,k1_relat_1(X24))
        | k1_funct_1(X24,X26) = k1_funct_1(X25,X26)
        | ~ r1_tarski(k1_relat_1(X24),k1_relat_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(esk1_2(X24,X25),k1_relat_1(X24))
        | r1_partfun1(X24,X25)
        | ~ r1_tarski(k1_relat_1(X24),k1_relat_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( k1_funct_1(X24,esk1_2(X24,X25)) != k1_funct_1(X25,esk1_2(X24,X25))
        | r1_partfun1(X24,X25)
        | ~ r1_tarski(k1_relat_1(X24),k1_relat_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_partfun1])])])])])).

cnf(c_0_15,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | r1_partfun1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X23 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X23 != k1_xboole_0
        | v1_funct_2(X23,X21,X22)
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_27,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(X1,esk5_0),k1_relat_1(X1))
    | r1_partfun1(X1,esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_23]),c_0_17])])).

cnf(c_0_31,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( r1_partfun1(esk4_0,esk5_0)
    | k1_funct_1(esk4_0,X1) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,k1_relset_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),k1_relat_1(esk4_0))
    | r1_partfun1(esk4_0,esk5_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_16]),c_0_32]),c_0_33])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_30])])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_funct_1(esk4_0,X1)
    | r1_partfun1(esk4_0,esk5_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk4_0,esk5_0),k1_relat_1(esk4_0))
    | r1_partfun1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_43,plain,
    ( r1_partfun1(X1,X2)
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0)) = k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0))
    | esk3_0 = k1_xboole_0
    | r1_partfun1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relset_1(esk2_0,esk3_0,esk4_0))
    | ~ r1_partfun1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_partfun1(esk4_0,esk5_0)
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_21]),c_0_29]),c_0_22]),c_0_30])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk4_0))
    | ~ r1_partfun1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_partfun1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_39]),c_0_40])])).

cnf(c_0_49,plain,
    ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
    | ~ r1_partfun1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk6_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_0) = k1_funct_1(X1,esk6_0)
    | esk3_0 = k1_xboole_0
    | ~ r1_partfun1(esk4_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_29]),c_0_30])])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk5_0,esk6_0) = k1_funct_1(esk4_0,esk6_0)
    | esk3_0 = k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_21]),c_0_22])])).

fof(c_0_53,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_0) != k1_funct_1(esk5_0,esk6_0)
    | ~ r1_partfun1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk5_0,esk6_0) = k1_funct_1(esk4_0,esk6_0)
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_39]),c_0_40])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_48])).

fof(c_0_59,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v4_relat_1(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_16])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61]),c_0_61]),c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_63]),c_0_22])])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = k1_funct_1(esk4_0,X1)
    | r1_partfun1(esk4_0,esk5_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk5_0),k1_xboole_0)
    | r1_partfun1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_64]),c_0_64]),c_0_62])])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | ~ r1_tarski(esk2_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0)) = k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0))
    | r1_partfun1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_61]),c_0_61]),c_0_62])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0)
    | ~ r1_partfun1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( r1_partfun1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_69]),c_0_21]),c_0_29]),c_0_22]),c_0_30]),c_0_64]),c_0_70]),c_0_62])])).

cnf(c_0_73,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = k1_funct_1(X2,X1)
    | ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_partfun1(esk4_0,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_64]),c_0_29]),c_0_30]),c_0_62])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk6_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(esk4_0,esk6_0) = k1_funct_1(X1,esk6_0)
    | ~ r1_partfun1(esk4_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(esk5_0,esk6_0) != k1_funct_1(esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_72])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_72]),c_0_21]),c_0_22])]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.38  # and selection function PSelectComplexPreferEQ.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t145_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(r1_partfun1(X3,X4)<=>![X5]:(r2_hidden(X5,k1_relset_1(X1,X2,X3))=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_2)).
% 0.20/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.38  fof(t132_partfun1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))=>(r1_partfun1(X1,X2)<=>![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 0.20/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(r1_partfun1(X3,X4)<=>![X5]:(r2_hidden(X5,k1_relset_1(X1,X2,X3))=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))))), inference(assume_negation,[status(cth)],[t145_funct_2])).
% 0.20/0.38  fof(c_0_11, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.38  fof(c_0_12, negated_conjecture, ![X33]:((v1_funct_1(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((esk3_0!=k1_xboole_0|esk2_0=k1_xboole_0)&(((r2_hidden(esk6_0,k1_relset_1(esk2_0,esk3_0,esk4_0))|~r1_partfun1(esk4_0,esk5_0))&(k1_funct_1(esk4_0,esk6_0)!=k1_funct_1(esk5_0,esk6_0)|~r1_partfun1(esk4_0,esk5_0)))&(r1_partfun1(esk4_0,esk5_0)|(~r2_hidden(X33,k1_relset_1(esk2_0,esk3_0,esk4_0))|k1_funct_1(esk4_0,X33)=k1_funct_1(esk5_0,X33))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.38  fof(c_0_14, plain, ![X24, X25, X26]:((~r1_partfun1(X24,X25)|(~r2_hidden(X26,k1_relat_1(X24))|k1_funct_1(X24,X26)=k1_funct_1(X25,X26))|~r1_tarski(k1_relat_1(X24),k1_relat_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)))&((r2_hidden(esk1_2(X24,X25),k1_relat_1(X24))|r1_partfun1(X24,X25)|~r1_tarski(k1_relat_1(X24),k1_relat_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(k1_funct_1(X24,esk1_2(X24,X25))!=k1_funct_1(X25,esk1_2(X24,X25))|r1_partfun1(X24,X25)|~r1_tarski(k1_relat_1(X24),k1_relat_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25))|(~v1_relat_1(X24)|~v1_funct_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_partfun1])])])])])).
% 0.20/0.38  cnf(c_0_15, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_17, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_18, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.38  fof(c_0_19, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|r1_partfun1(X1,X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_24, plain, ![X21, X22, X23]:((((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))&((~v1_funct_2(X23,X21,X22)|X23=k1_xboole_0|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X23!=k1_xboole_0|v1_funct_2(X23,X21,X22)|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.38  cnf(c_0_25, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  fof(c_0_26, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.38  cnf(c_0_27, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(X1,esk5_0),k1_relat_1(X1))|r1_partfun1(X1,esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_23]), c_0_17])])).
% 0.20/0.38  cnf(c_0_31, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_16])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_34, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_23])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (r1_partfun1(esk4_0,esk5_0)|k1_funct_1(esk4_0,X1)=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,k1_relset_1(esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk5_0),k1_relat_1(esk4_0))|r1_partfun1(esk4_0,esk5_0)|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_16]), c_0_32]), c_0_33])])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_30])])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_funct_1(esk4_0,X1)|r1_partfun1(esk4_0,esk5_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_2(esk4_0,esk5_0),k1_relat_1(esk4_0))|r1_partfun1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.20/0.38  cnf(c_0_43, plain, (r1_partfun1(X1,X2)|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0))=k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0))|esk3_0=k1_xboole_0|r1_partfun1(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk6_0,k1_relset_1(esk2_0,esk3_0,esk4_0))|~r1_partfun1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (esk3_0=k1_xboole_0|r1_partfun1(esk4_0,esk5_0)|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_21]), c_0_29]), c_0_22]), c_0_30])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk4_0))|~r1_partfun1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_45, c_0_37])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (esk3_0=k1_xboole_0|r1_partfun1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_39]), c_0_40])])).
% 0.20/0.38  cnf(c_0_49, plain, (k1_funct_1(X1,X3)=k1_funct_1(X2,X3)|~r1_partfun1(X1,X2)|~r2_hidden(X3,k1_relat_1(X1))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk6_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk4_0,esk6_0)=k1_funct_1(X1,esk6_0)|esk3_0=k1_xboole_0|~r1_partfun1(esk4_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_29]), c_0_30])])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk4_0,esk6_0)|esk3_0=k1_xboole_0|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_21]), c_0_22])])).
% 0.20/0.38  fof(c_0_53, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk4_0,esk6_0)!=k1_funct_1(esk5_0,esk6_0)|~r1_partfun1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (k1_funct_1(esk5_0,esk6_0)=k1_funct_1(esk4_0,esk6_0)|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_39]), c_0_40])])).
% 0.20/0.38  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_48])).
% 0.20/0.38  fof(c_0_59, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.38  cnf(c_0_60, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|~r1_tarski(esk2_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_40])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 0.20/0.38  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.38  cnf(c_0_63, negated_conjecture, (v4_relat_1(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_16])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61]), c_0_61]), c_0_62])])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_63]), c_0_22])])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (k1_funct_1(esk5_0,X1)=k1_funct_1(esk4_0,X1)|r1_partfun1(esk4_0,esk5_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_41, c_0_64])).
% 0.20/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk5_0),k1_xboole_0)|r1_partfun1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_64]), c_0_64]), c_0_62])])).
% 0.20/0.38  cnf(c_0_68, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0|~r1_tarski(esk2_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_56, c_0_65])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk5_0,esk1_2(esk4_0,esk5_0))=k1_funct_1(esk4_0,esk1_2(esk4_0,esk5_0))|r1_partfun1(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_61]), c_0_61]), c_0_62])])).
% 0.20/0.38  cnf(c_0_71, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)|~r1_partfun1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_47, c_0_64])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, (r1_partfun1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_69]), c_0_21]), c_0_29]), c_0_22]), c_0_30]), c_0_64]), c_0_70]), c_0_62])])).
% 0.20/0.38  cnf(c_0_73, negated_conjecture, (k1_funct_1(esk4_0,X1)=k1_funct_1(X2,X1)|~r2_hidden(X1,k1_xboole_0)|~r1_partfun1(esk4_0,X2)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_64]), c_0_29]), c_0_30]), c_0_62])])).
% 0.20/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(esk6_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.20/0.38  cnf(c_0_75, negated_conjecture, (k1_funct_1(esk4_0,esk6_0)=k1_funct_1(X1,esk6_0)|~r1_partfun1(esk4_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.38  cnf(c_0_76, negated_conjecture, (k1_funct_1(esk5_0,esk6_0)!=k1_funct_1(esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_72])])).
% 0.20/0.38  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_72]), c_0_21]), c_0_22])]), c_0_76]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 78
% 0.20/0.38  # Proof object clause steps            : 57
% 0.20/0.38  # Proof object formula steps           : 21
% 0.20/0.38  # Proof object conjectures             : 49
% 0.20/0.38  # Proof object clause conjectures      : 46
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 10
% 0.20/0.38  # Proof object generating inferences   : 27
% 0.20/0.38  # Proof object simplifying inferences  : 71
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 29
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 29
% 0.20/0.38  # Processed clauses                    : 156
% 0.20/0.38  # ...of these trivial                  : 12
% 0.20/0.38  # ...subsumed                          : 11
% 0.20/0.38  # ...remaining for further processing  : 133
% 0.20/0.38  # Other redundant clauses eliminated   : 9
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 5
% 0.20/0.38  # Backward-rewritten                   : 42
% 0.20/0.38  # Generated clauses                    : 128
% 0.20/0.38  # ...of the previous two non-trivial   : 113
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 111
% 0.20/0.38  # Factorizations                       : 8
% 0.20/0.38  # Equation resolutions                 : 10
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
% 0.20/0.38  # Current number of processed clauses  : 52
% 0.20/0.38  #    Positive orientable unit clauses  : 26
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 25
% 0.20/0.38  # Current number of unprocessed clauses: 12
% 0.20/0.38  # ...number of literals in the above   : 77
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 75
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 691
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 259
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 16
% 0.20/0.38  # Unit Clause-clause subsumption calls : 76
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 11
% 0.20/0.38  # BW rewrite match successes           : 6
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4708
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.041 s
% 0.20/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
