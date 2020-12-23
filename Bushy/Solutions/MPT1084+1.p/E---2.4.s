%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t201_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:41 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 160 expanded)
%              Number of clauses        :   27 (  57 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  165 ( 694 expanded)
%              Number of equality atoms :   22 (  94 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   25 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',t201_funct_2)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',fc3_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',redefinition_k6_partfun1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',redefinition_k3_funct_2)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',d9_funct_2)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',dt_k6_partfun1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',t2_subset)).

fof(t35_funct_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',t35_funct_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t201_funct_2.p',cc1_funct_2)).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X64] :
      ( v1_relat_1(k6_relat_1(X64))
      & v1_funct_1(k6_relat_1(X64)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_12,plain,(
    ! [X29] : k6_partfun1(X29) = k6_relat_1(X29) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_13,negated_conjecture,(
    ! [X8] :
      ( ~ v1_xboole_0(esk1_0)
      & v1_funct_1(esk2_0)
      & v1_funct_2(esk2_0,esk1_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
      & ( ~ m1_subset_1(X8,esk1_0)
        | k3_funct_2(esk1_0,esk1_0,esk2_0,X8) = X8 )
      & ~ r2_funct_2(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_14,plain,(
    ! [X25,X26,X27,X28] :
      ( v1_xboole_0(X25)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,X25,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | ~ m1_subset_1(X28,X25)
      | k3_funct_2(X25,X26,X27,X28) = k1_funct_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_15,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r2_funct_2(X11,X12,X13,X14)
        | ~ m1_subset_1(X15,X11)
        | k1_funct_1(X13,X15) = k1_funct_1(X14,X15)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( m1_subset_1(esk3_4(X11,X12,X13,X14),X11)
        | r2_funct_2(X11,X12,X13,X14)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( k1_funct_1(X13,esk3_4(X11,X12,X13,X14)) != k1_funct_1(X14,esk3_4(X11,X12,X13,X14))
        | r2_funct_2(X11,X12,X13,X14)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

fof(c_0_16,plain,(
    ! [X21] :
      ( v1_partfun1(k6_partfun1(X21),X21)
      & m1_subset_1(k6_partfun1(X21),k1_zfmisc_1(k2_zfmisc_1(X21,X21))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_17,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k3_funct_2(esk1_0,esk1_0,esk2_0,X1) = X1
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | m1_subset_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_26,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X44,X45)
      | v1_xboole_0(X45)
      | r2_hidden(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_funct_2(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),X1)
    | r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( v1_funct_1(k6_partfun1(X1)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_31,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk3_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk3_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = X1
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_4(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0)),esk1_0)
    | ~ v1_funct_2(k6_partfun1(esk1_0),esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_21]),c_0_22]),c_0_30]),c_0_23])])).

fof(c_0_36,plain,(
    ! [X46,X47] :
      ( ~ r2_hidden(X46,X47)
      | k1_funct_1(k6_relat_1(X47),X46) = X46 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_4(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0))) != k1_funct_1(k6_partfun1(esk1_0),esk3_4(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0)))
    | ~ v1_funct_2(k6_partfun1(esk1_0),esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_29]),c_0_21]),c_0_22]),c_0_30]),c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = X1
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_4(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0)),esk1_0)
    | ~ v1_funct_2(k6_partfun1(esk1_0),esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24])).

cnf(c_0_40,plain,
    ( k1_funct_1(k6_relat_1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(k6_partfun1(esk1_0),esk3_4(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0))) != esk3_4(esk1_0,esk1_0,esk2_0,k6_partfun1(esk1_0))
    | ~ v1_funct_2(k6_partfun1(esk1_0),esk1_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_42,plain,
    ( k1_funct_1(k6_partfun1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_18])).

fof(c_0_43,plain,(
    ! [X61,X62,X63] :
      ( ( v1_funct_1(X63)
        | ~ v1_funct_1(X63)
        | ~ v1_partfun1(X63,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( v1_funct_2(X63,X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_partfun1(X63,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_2(k6_partfun1(esk1_0),esk1_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_39])).

cnf(c_0_45,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_29]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
