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
% DateTime   : Thu Dec  3 11:08:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 358 expanded)
%              Number of clauses        :   33 ( 128 expanded)
%              Number of leaves         :   11 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  226 (1660 expanded)
%              Number of equality atoms :   45 ( 229 expanded)
%              Maximal formula depth    :   14 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

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

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

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

fof(c_0_13,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_14,negated_conjecture,(
    ! [X34] :
      ( ~ v1_xboole_0(esk2_0)
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk2_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
      & ( ~ m1_subset_1(X34,esk2_0)
        | k3_funct_2(esk2_0,esk2_0,esk3_0,X34) = X34 )
      & ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_15,plain,(
    ! [X9,X10] : v1_relat_1(k2_zfmisc_1(X9,X10)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
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

fof(c_0_21,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_22,plain,(
    ! [X23,X24,X25,X26] :
      ( v1_xboole_0(X23)
      | ~ v1_funct_1(X25)
      | ~ v1_funct_2(X25,X23,X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ m1_subset_1(X26,X23)
      | k3_funct_2(X23,X24,X25,X26) = k1_funct_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X6,X5)
        | r2_hidden(X6,X5)
        | v1_xboole_0(X5) )
      & ( ~ r2_hidden(X6,X5)
        | m1_subset_1(X6,X5)
        | v1_xboole_0(X5) )
      & ( ~ m1_subset_1(X6,X5)
        | v1_xboole_0(X6)
        | ~ v1_xboole_0(X5) )
      & ( ~ v1_xboole_0(X6)
        | m1_subset_1(X6,X5)
        | ~ v1_xboole_0(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_24,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) = esk3_0
    | r2_hidden(esk1_2(k1_relat_1(esk3_0),esk3_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_35,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v1_partfun1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_29]),c_0_25])]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v4_relat_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

fof(c_0_38,plain,(
    ! [X27] : k6_partfun1(X27) = k6_relat_1(X27) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_39,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk1_2(X2,X1)) != esk1_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_29]),c_0_25])]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) = esk3_0
    | m1_subset_1(esk1_2(k1_relat_1(esk3_0),esk3_0),k1_relat_1(esk3_0))
    | v1_xboole_0(k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_26])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1)) != esk1_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_30])).

fof(c_0_49,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ r2_funct_2(X28,X29,X30,X31)
        | X30 = X31
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( X30 != X31
        | r2_funct_2(X28,X29,X30,X31)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43]),c_0_25]),c_0_26]),c_0_43])]),c_0_48])).

cnf(c_0_52,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29]),c_0_25]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:40:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.029 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t201_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 0.12/0.36  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.12/0.36  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.36  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.36  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.12/0.36  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.36  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.12/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.12/0.36  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.12/0.36  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.12/0.36  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.12/0.36  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t201_funct_2])).
% 0.12/0.36  fof(c_0_12, plain, ![X11, X12, X13]:(((k1_relat_1(X12)=X11|X12!=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(~r2_hidden(X13,X11)|k1_funct_1(X12,X13)=X13|X12!=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((r2_hidden(esk1_2(X11,X12),X11)|k1_relat_1(X12)!=X11|X12=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_funct_1(X12,esk1_2(X11,X12))!=esk1_2(X11,X12)|k1_relat_1(X12)!=X11|X12=k6_relat_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.12/0.36  fof(c_0_13, plain, ![X7, X8]:(~v1_relat_1(X7)|(~m1_subset_1(X8,k1_zfmisc_1(X7))|v1_relat_1(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.36  fof(c_0_14, negated_conjecture, ![X34]:(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&((~m1_subset_1(X34,esk2_0)|k3_funct_2(esk2_0,esk2_0,esk3_0,X34)=X34)&~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.12/0.36  fof(c_0_15, plain, ![X9, X10]:v1_relat_1(k2_zfmisc_1(X9,X10)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.36  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_17, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_19, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  fof(c_0_20, plain, ![X18, X19, X20]:((v1_funct_1(X20)|(~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|v1_xboole_0(X19))&(v1_partfun1(X20,X18)|(~v1_funct_1(X20)|~v1_funct_2(X20,X18,X19))|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|v1_xboole_0(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.12/0.36  fof(c_0_21, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.36  fof(c_0_22, plain, ![X23, X24, X25, X26]:(v1_xboole_0(X23)|~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|~m1_subset_1(X26,X23)|k3_funct_2(X23,X24,X25,X26)=k1_funct_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.12/0.36  fof(c_0_23, plain, ![X5, X6]:(((~m1_subset_1(X6,X5)|r2_hidden(X6,X5)|v1_xboole_0(X5))&(~r2_hidden(X6,X5)|m1_subset_1(X6,X5)|v1_xboole_0(X5)))&((~m1_subset_1(X6,X5)|v1_xboole_0(X6)|~v1_xboole_0(X5))&(~v1_xboole_0(X6)|m1_subset_1(X6,X5)|~v1_xboole_0(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.12/0.36  cnf(c_0_24, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.12/0.36  fof(c_0_27, plain, ![X21, X22]:((~v1_partfun1(X22,X21)|k1_relat_1(X22)=X21|(~v1_relat_1(X22)|~v4_relat_1(X22,X21)))&(k1_relat_1(X22)!=X21|v1_partfun1(X22,X21)|(~v1_relat_1(X22)|~v4_relat_1(X22,X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.12/0.36  cnf(c_0_28, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_31, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_32, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.36  cnf(c_0_33, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (k6_relat_1(k1_relat_1(esk3_0))=esk3_0|r2_hidden(esk1_2(k1_relat_1(esk3_0),esk3_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.12/0.36  cnf(c_0_35, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_36, negated_conjecture, (v1_partfun1(esk3_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_29]), c_0_25])]), c_0_30])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, (v4_relat_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 0.12/0.36  fof(c_0_38, plain, ![X27]:k6_partfun1(X27)=k6_relat_1(X27), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.12/0.36  cnf(c_0_39, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk1_2(X2,X1))!=esk1_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_40, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,X1)=X1|~m1_subset_1(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_41, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,X1)=k1_funct_1(esk3_0,X1)|~m1_subset_1(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_29]), c_0_25])]), c_0_30])).
% 0.12/0.36  cnf(c_0_42, negated_conjecture, (k6_relat_1(k1_relat_1(esk3_0))=esk3_0|m1_subset_1(esk1_2(k1_relat_1(esk3_0),esk3_0),k1_relat_1(esk3_0))|v1_xboole_0(k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.36  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_26])])).
% 0.12/0.36  cnf(c_0_44, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  cnf(c_0_45, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.36  cnf(c_0_46, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1))!=esk1_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_39])).
% 0.12/0.36  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk3_0,X1)=X1|~m1_subset_1(X1,esk2_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.36  cnf(c_0_48, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_30])).
% 0.12/0.36  fof(c_0_49, plain, ![X28, X29, X30, X31]:((~r2_funct_2(X28,X29,X30,X31)|X30=X31|(~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))&(X30!=X31|r2_funct_2(X28,X29,X30,X31)|(~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.12/0.36  cnf(c_0_50, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.36  cnf(c_0_51, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_43]), c_0_25]), c_0_26]), c_0_43])]), c_0_48])).
% 0.12/0.36  cnf(c_0_52, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.36  cnf(c_0_53, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.12/0.36  cnf(c_0_54, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_52])).
% 0.12/0.36  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29]), c_0_25]), c_0_18])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 56
% 0.12/0.36  # Proof object clause steps            : 33
% 0.12/0.36  # Proof object formula steps           : 23
% 0.12/0.36  # Proof object conjectures             : 22
% 0.12/0.36  # Proof object clause conjectures      : 19
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 17
% 0.12/0.36  # Proof object initial formulas used   : 11
% 0.12/0.36  # Proof object generating inferences   : 10
% 0.12/0.36  # Proof object simplifying inferences  : 35
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 11
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 26
% 0.12/0.36  # Removed in clause preprocessing      : 2
% 0.12/0.36  # Initial clauses in saturation        : 24
% 0.12/0.36  # Processed clauses                    : 77
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 5
% 0.12/0.36  # ...remaining for further processing  : 72
% 0.12/0.36  # Other redundant clauses eliminated   : 6
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 6
% 0.12/0.36  # Generated clauses                    : 35
% 0.12/0.36  # ...of the previous two non-trivial   : 31
% 0.12/0.36  # Contextual simplify-reflections      : 1
% 0.12/0.36  # Paramodulations                      : 29
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 6
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 36
% 0.12/0.36  #    Positive orientable unit clauses  : 10
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 2
% 0.12/0.36  #    Non-unit-clauses                  : 24
% 0.12/0.36  # Current number of unprocessed clauses: 2
% 0.12/0.36  # ...number of literals in the above   : 4
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 31
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 157
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 32
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 5
% 0.12/0.36  # Unit Clause-clause subsumption calls : 21
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 2
% 0.12/0.36  # BW rewrite match successes           : 2
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 2935
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.034 s
% 0.12/0.36  # System time              : 0.003 s
% 0.12/0.36  # Total time               : 0.036 s
% 0.12/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
