%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:25 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 322 expanded)
%              Number of clauses        :   32 ( 114 expanded)
%              Number of leaves         :   11 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  197 (1481 expanded)
%              Number of equality atoms :   40 ( 207 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t201_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_funct_2(X2,X1,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => k3_funct_2(X1,X1,X2,X3) = X3 )
           => r2_funct_2(X1,X1,X2,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(reflexivity_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_funct_2(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_funct_2(X2,X1,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( ! [X3] :
                  ( m1_subset_1(X3,X1)
                 => k3_funct_2(X1,X1,X2,X3) = X3 )
             => r2_funct_2(X1,X1,X2,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t201_funct_2])).

fof(c_0_12,plain,(
    ! [X18,X19,X20] :
      ( ( v1_funct_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | v1_xboole_0(X19) )
      & ( v1_partfun1(X20,X18)
        | ~ v1_funct_1(X20)
        | ~ v1_funct_2(X20,X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | v1_xboole_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X34] :
      ( ~ v1_xboole_0(esk2_0)
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk2_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
      & ( ~ m1_subset_1(X34,esk2_0)
        | k3_funct_2(esk2_0,esk2_0,esk3_0,X34) = X34 )
      & ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_16,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X11,X12,X13] :
      ( ( k1_relat_1(X12) = X11
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X13,X11)
        | k1_funct_1(X12,X13) = X13
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | k1_relat_1(X12) != X11
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_funct_1(X12,esk1_2(X11,X12)) != esk1_2(X11,X12)
        | k1_relat_1(X12) != X11
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( ( ~ v1_partfun1(X22,X21)
        | k1_relat_1(X22) = X21
        | ~ v1_relat_1(X22)
        | ~ v4_relat_1(X22,X21) )
      & ( k1_relat_1(X22) != X21
        | v1_partfun1(X22,X21)
        | ~ v1_relat_1(X22)
        | ~ v4_relat_1(X22,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_19,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_27,plain,(
    ! [X23,X24,X25,X26] :
      ( v1_xboole_0(X23)
      | ~ v1_funct_1(X25)
      | ~ v1_funct_2(X25,X23,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ m1_subset_1(X26,X23)
      | k3_funct_2(X23,X24,X25,X26) = k1_funct_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v1_partfun1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v4_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_26])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | m1_subset_1(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_35,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

fof(c_0_37,plain,(
    ! [X27] : k6_partfun1(X27) = k6_relat_1(X27) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_38,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk1_2(X2,X1)) != esk1_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_36]),c_0_36]),c_0_36]),c_0_32])])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1)) != esk1_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_48,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,X28,X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,X28,X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | r2_funct_2(X28,X29,X30,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_36]),c_0_22]),c_0_32]),c_0_36])]),c_0_47])).

cnf(c_0_51,plain,
    ( r2_funct_2(X2,X3,X1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_funct_2(esk2_0,esk2_0,X1,X1)
    | ~ v1_funct_2(X1,esk2_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_21]),c_0_22]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.07/0.29  % Computer   : n023.cluster.edu
% 0.07/0.29  % Model      : x86_64 x86_64
% 0.07/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.29  % Memory     : 8042.1875MB
% 0.07/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.29  % CPULimit   : 60
% 0.07/0.29  % WCLimit    : 600
% 0.07/0.29  % DateTime   : Tue Dec  1 15:24:20 EST 2020
% 0.07/0.29  % CPUTime    : 
% 0.07/0.29  # Version: 2.5pre002
% 0.07/0.30  # No SInE strategy applied
% 0.07/0.30  # Trying AutoSched0 for 299 seconds
% 0.15/0.33  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.15/0.33  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.15/0.33  #
% 0.15/0.33  # Preprocessing time       : 0.027 s
% 0.15/0.33  # Presaturation interreduction done
% 0.15/0.33  
% 0.15/0.33  # Proof found!
% 0.15/0.33  # SZS status Theorem
% 0.15/0.33  # SZS output start CNFRefutation
% 0.15/0.33  fof(t201_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 0.15/0.33  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.15/0.33  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.15/0.33  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.15/0.33  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.15/0.33  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 0.15/0.33  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.15/0.33  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.15/0.33  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.15/0.33  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.15/0.33  fof(reflexivity_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_funct_2(X1,X2,X3,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 0.15/0.33  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t201_funct_2])).
% 0.15/0.33  fof(c_0_12, plain, ![X18, X19, X20]:((v1_funct_1(X20)|(~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|v1_xboole_0(X19))&(v1_partfun1(X20,X18)|(~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|v1_xboole_0(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.15/0.33  fof(c_0_13, negated_conjecture, ![X34]:(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&((~m1_subset_1(X34,esk2_0)|k3_funct_2(esk2_0,esk2_0,esk3_0,X34)=X34)&~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.15/0.33  fof(c_0_14, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.15/0.33  fof(c_0_15, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.15/0.33  fof(c_0_16, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.15/0.33  fof(c_0_17, plain, ![X11, X12, X13]:(((k1_relat_1(X12)=X11|X12!=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(~r2_hidden(X13,X11)|k1_funct_1(X12,X13)=X13|X12!=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((r2_hidden(esk1_2(X11,X12),X11)|k1_relat_1(X12)!=X11|X12=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_funct_1(X12,esk1_2(X11,X12))!=esk1_2(X11,X12)|k1_relat_1(X12)!=X11|X12=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.15/0.33  fof(c_0_18, plain, ![X21, X22]:((~v1_partfun1(X22,X21)|k1_relat_1(X22)=X21|(~v1_relat_1(X22)|~v4_relat_1(X22,X21)))&(k1_relat_1(X22)!=X21|v1_partfun1(X22,X21)|(~v1_relat_1(X22)|~v4_relat_1(X22,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.15/0.33  cnf(c_0_19, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.15/0.33  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_21, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_23, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_24, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.33  cnf(c_0_25, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.33  cnf(c_0_26, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.33  fof(c_0_27, plain, ![X23, X24, X25, X26]:(v1_xboole_0(X23)|~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X26,X23)|k3_funct_2(X23,X24,X25,X26)=k1_funct_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.15/0.33  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.33  cnf(c_0_29, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.15/0.33  cnf(c_0_30, negated_conjecture, (v1_partfun1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.33  cnf(c_0_31, negated_conjecture, (v4_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 0.15/0.33  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_26])])).
% 0.15/0.33  cnf(c_0_33, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.15/0.33  fof(c_0_34, plain, ![X5, X6]:(~r2_hidden(X5,X6)|m1_subset_1(X5,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.15/0.33  cnf(c_0_35, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_28])).
% 0.15/0.33  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.15/0.33  fof(c_0_37, plain, ![X27]:k6_partfun1(X27)=k6_relat_1(X27), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.15/0.33  cnf(c_0_38, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk1_2(X2,X1))!=esk1_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.33  cnf(c_0_39, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,X1)=X1|~m1_subset_1(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_40, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,X1)=k1_funct_1(esk3_0,X1)|~m1_subset_1(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.33  cnf(c_0_41, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.15/0.33  cnf(c_0_42, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_22]), c_0_36]), c_0_36]), c_0_36]), c_0_32])])).
% 0.15/0.33  cnf(c_0_43, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.33  cnf(c_0_44, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.15/0.33  cnf(c_0_45, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1))!=esk1_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_38])).
% 0.15/0.33  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk3_0,X1)=X1|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.15/0.33  cnf(c_0_47, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.15/0.33  fof(c_0_48, plain, ![X28, X29, X30, X31]:(~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|r2_funct_2(X28,X29,X30,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).
% 0.15/0.33  cnf(c_0_49, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.15/0.33  cnf(c_0_50, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_36]), c_0_22]), c_0_32]), c_0_36])]), c_0_47])).
% 0.15/0.33  cnf(c_0_51, plain, (r2_funct_2(X2,X3,X1,X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.15/0.33  cnf(c_0_52, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.15/0.33  cnf(c_0_53, negated_conjecture, (r2_funct_2(esk2_0,esk2_0,X1,X1)|~v1_funct_2(X1,esk2_0,esk2_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_20]), c_0_21]), c_0_22])])).
% 0.15/0.33  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_21]), c_0_22]), c_0_20])]), ['proof']).
% 0.15/0.33  # SZS output end CNFRefutation
% 0.15/0.33  # Proof object total steps             : 55
% 0.15/0.33  # Proof object clause steps            : 32
% 0.15/0.33  # Proof object formula steps           : 23
% 0.15/0.33  # Proof object conjectures             : 22
% 0.15/0.33  # Proof object clause conjectures      : 19
% 0.15/0.33  # Proof object formula conjectures     : 3
% 0.15/0.33  # Proof object initial clauses used    : 17
% 0.15/0.33  # Proof object initial formulas used   : 11
% 0.15/0.33  # Proof object generating inferences   : 11
% 0.15/0.33  # Proof object simplifying inferences  : 35
% 0.15/0.33  # Training examples: 0 positive, 0 negative
% 0.15/0.33  # Parsed axioms                        : 11
% 0.15/0.33  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.33  # Initial clauses                      : 22
% 0.15/0.33  # Removed in clause preprocessing      : 2
% 0.15/0.33  # Initial clauses in saturation        : 20
% 0.15/0.33  # Processed clauses                    : 62
% 0.15/0.33  # ...of these trivial                  : 0
% 0.15/0.33  # ...subsumed                          : 1
% 0.15/0.33  # ...remaining for further processing  : 61
% 0.15/0.33  # Other redundant clauses eliminated   : 5
% 0.15/0.33  # Clauses deleted for lack of memory   : 0
% 0.15/0.33  # Backward-subsumed                    : 0
% 0.15/0.33  # Backward-rewritten                   : 4
% 0.15/0.33  # Generated clauses                    : 29
% 0.15/0.33  # ...of the previous two non-trivial   : 23
% 0.15/0.33  # Contextual simplify-reflections      : 1
% 0.15/0.33  # Paramodulations                      : 24
% 0.15/0.33  # Factorizations                       : 0
% 0.15/0.33  # Equation resolutions                 : 5
% 0.15/0.33  # Propositional unsat checks           : 0
% 0.15/0.33  #    Propositional check models        : 0
% 0.15/0.33  #    Propositional check unsatisfiable : 0
% 0.15/0.33  #    Propositional clauses             : 0
% 0.15/0.33  #    Propositional clauses after purity: 0
% 0.15/0.33  #    Propositional unsat core size     : 0
% 0.15/0.33  #    Propositional preprocessing time  : 0.000
% 0.15/0.33  #    Propositional encoding time       : 0.000
% 0.15/0.33  #    Propositional solver time         : 0.000
% 0.15/0.33  #    Success case prop preproc time    : 0.000
% 0.15/0.33  #    Success case prop encoding time   : 0.000
% 0.15/0.33  #    Success case prop solver time     : 0.000
% 0.15/0.33  # Current number of processed clauses  : 32
% 0.15/0.33  #    Positive orientable unit clauses  : 10
% 0.15/0.33  #    Positive unorientable unit clauses: 0
% 0.15/0.33  #    Negative unit clauses             : 2
% 0.15/0.33  #    Non-unit-clauses                  : 20
% 0.15/0.33  # Current number of unprocessed clauses: 0
% 0.15/0.33  # ...number of literals in the above   : 0
% 0.15/0.33  # Current number of archived formulas  : 0
% 0.15/0.33  # Current number of archived clauses   : 25
% 0.15/0.33  # Clause-clause subsumption calls (NU) : 124
% 0.15/0.33  # Rec. Clause-clause subsumption calls : 18
% 0.15/0.33  # Non-unit clause-clause subsumptions  : 2
% 0.15/0.33  # Unit Clause-clause subsumption calls : 3
% 0.15/0.33  # Rewrite failures with RHS unbound    : 0
% 0.15/0.33  # BW rewrite match attempts            : 1
% 0.15/0.33  # BW rewrite match successes           : 1
% 0.15/0.33  # Condensation attempts                : 0
% 0.15/0.33  # Condensation successes               : 0
% 0.15/0.33  # Termbank termtop insertions          : 2554
% 0.15/0.33  
% 0.15/0.33  # -------------------------------------------------
% 0.15/0.33  # User time                : 0.029 s
% 0.15/0.33  # System time              : 0.005 s
% 0.15/0.33  # Total time               : 0.034 s
% 0.15/0.33  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
