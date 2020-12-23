%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 248 expanded)
%              Number of clauses        :   35 (  95 expanded)
%              Number of leaves         :    9 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  207 (1184 expanded)
%              Number of equality atoms :   57 ( 230 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   19 (   3 average)
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

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X26,X27] :
      ( ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,X26,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26)))
      | k1_relset_1(X26,X26,X27) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

fof(c_0_11,negated_conjecture,(
    ! [X30] :
      ( ~ v1_xboole_0(esk2_0)
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk2_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
      & ( ~ m1_subset_1(X30,esk2_0)
        | k3_funct_2(esk2_0,esk2_0,esk3_0,X30) = X30 )
      & ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ( k1_relat_1(X8) = X7
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(X9,X7)
        | k1_funct_1(X8,X9) = X9
        | X8 != k6_relat_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | k1_relat_1(X8) != X7
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( k1_funct_1(X8,esk1_2(X7,X8)) != esk1_2(X7,X8)
        | k1_relat_1(X8) != X7
        | X8 = k6_relat_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_14,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k1_relset_1(X1,X1,esk3_0) = X1
    | ~ v1_funct_2(esk3_0,X1,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( k1_relset_1(esk2_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X17,X18,X19,X20] :
      ( v1_xboole_0(X17)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,X17,X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ m1_subset_1(X20,X17)
      | k3_funct_2(X17,X18,X19,X20) = k1_funct_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_25,plain,(
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

cnf(c_0_26,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_17])])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk1_2(X2,X1)) != esk1_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_34,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r2_funct_2(X22,X23,X24,X25)
        | X24 = X25
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X24 != X25
        | r2_funct_2(X22,X23,X24,X25)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_35,negated_conjecture,
    ( k3_funct_2(X1,X2,esk3_0,X3) = k1_funct_1(esk3_0,X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(esk3_0,X1,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1)) != esk1_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_39,plain,(
    ! [X21] : k6_partfun1(X21) = k6_relat_1(X21) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_40,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( k3_funct_2(esk2_0,X1,esk3_0,esk1_2(esk2_0,esk3_0)) = k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))
    | k6_relat_1(esk2_0) = esk3_0
    | ~ v1_funct_2(esk3_0,esk2_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) = esk3_0
    | k1_funct_1(esk3_0,esk1_2(k1_relat_1(esk3_0),esk3_0)) != esk1_2(k1_relat_1(esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_15]),c_0_28])])).

cnf(c_0_43,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,esk1_2(esk2_0,esk3_0)) = esk1_2(esk2_0,esk3_0)
    | k6_relat_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,esk1_2(esk2_0,esk3_0)) = k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))
    | k6_relat_1(esk2_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_17])])).

cnf(c_0_48,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0)) != esk1_2(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_27]),c_0_27]),c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( r2_funct_2(X1,X2,esk3_0,esk3_0)
    | ~ v1_funct_2(esk3_0,X1,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_21]),c_0_17])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:29:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.12/0.39  # and selection function HSelectMinInfpos.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.050 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t201_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 0.12/0.39  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.12/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.39  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.12/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.39  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.12/0.39  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.12/0.39  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.12/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.12/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t201_funct_2])).
% 0.12/0.39  fof(c_0_10, plain, ![X26, X27]:(~v1_funct_1(X27)|~v1_funct_2(X27,X26,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X26,X26)))|k1_relset_1(X26,X26,X27)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.12/0.39  fof(c_0_11, negated_conjecture, ![X30]:(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&((~m1_subset_1(X30,esk2_0)|k3_funct_2(esk2_0,esk2_0,esk3_0,X30)=X30)&~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.12/0.39  fof(c_0_12, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k1_relset_1(X14,X15,X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.39  fof(c_0_13, plain, ![X7, X8, X9]:(((k1_relat_1(X8)=X7|X8!=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(~r2_hidden(X9,X7)|k1_funct_1(X8,X9)=X9|X8!=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&((r2_hidden(esk1_2(X7,X8),X7)|k1_relat_1(X8)!=X7|X8=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(k1_funct_1(X8,esk1_2(X7,X8))!=esk1_2(X7,X8)|k1_relat_1(X8)!=X7|X8=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.12/0.39  cnf(c_0_14, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_16, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  fof(c_0_18, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.39  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_20, negated_conjecture, (k1_relset_1(X1,X1,esk3_0)=X1|~v1_funct_2(esk3_0,X1,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_22, negated_conjecture, (k1_relset_1(esk2_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.39  cnf(c_0_23, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  fof(c_0_24, plain, ![X17, X18, X19, X20]:(v1_xboole_0(X17)|~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|~m1_subset_1(X20,X17)|k3_funct_2(X17,X18,X19,X20)=k1_funct_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.12/0.39  fof(c_0_25, plain, ![X5, X6]:(((~m1_subset_1(X6,X5)|r2_hidden(X6,X5)|v1_xboole_0(X5))&(~r2_hidden(X6,X5)|m1_subset_1(X6,X5)|v1_xboole_0(X5)))&((~m1_subset_1(X6,X5)|v1_xboole_0(X6)|~v1_xboole_0(X5))&(~v1_xboole_0(X6)|m1_subset_1(X6,X5)|~v1_xboole_0(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.12/0.39  cnf(c_0_26, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_17])])).
% 0.12/0.39  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_17])).
% 0.12/0.39  cnf(c_0_29, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.39  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_15]), c_0_28])])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_33, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk1_2(X2,X1))!=esk1_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  fof(c_0_34, plain, ![X22, X23, X24, X25]:((~r2_funct_2(X22,X23,X24,X25)|X24=X25|(~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~v1_funct_1(X25)|~v1_funct_2(X25,X22,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&(X24!=X25|r2_funct_2(X22,X23,X24,X25)|(~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~v1_funct_1(X25)|~v1_funct_2(X25,X22,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (k3_funct_2(X1,X2,esk3_0,X3)=k1_funct_1(esk3_0,X3)|v1_xboole_0(X1)|~v1_funct_2(esk3_0,X1,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_15])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.12/0.39  cnf(c_0_37, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1))!=esk1_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_38, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.39  fof(c_0_39, plain, ![X21]:k6_partfun1(X21)=k6_relat_1(X21), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,X1)=X1|~m1_subset_1(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (k3_funct_2(esk2_0,X1,esk3_0,esk1_2(esk2_0,esk3_0))=k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))|k6_relat_1(esk2_0)=esk3_0|~v1_funct_2(esk3_0,esk2_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_32])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (k6_relat_1(k1_relat_1(esk3_0))=esk3_0|k1_funct_1(esk3_0,esk1_2(k1_relat_1(esk3_0),esk3_0))!=esk1_2(k1_relat_1(esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_15]), c_0_28])])).
% 0.12/0.39  cnf(c_0_43, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_38])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_45, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,esk1_2(esk2_0,esk3_0))=esk1_2(esk2_0,esk3_0)|k6_relat_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,esk1_2(esk2_0,esk3_0))=k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))|k6_relat_1(esk2_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_17])])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))!=esk1_2(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_27]), c_0_27]), c_0_27])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (r2_funct_2(X1,X2,esk3_0,esk3_0)|~v1_funct_2(esk3_0,X1,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_15])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.12/0.39  cnf(c_0_52, negated_conjecture, (r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_21]), c_0_17])])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51]), c_0_52])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 54
% 0.12/0.39  # Proof object clause steps            : 35
% 0.12/0.39  # Proof object formula steps           : 19
% 0.12/0.39  # Proof object conjectures             : 26
% 0.12/0.39  # Proof object clause conjectures      : 23
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 15
% 0.12/0.39  # Proof object initial formulas used   : 9
% 0.12/0.39  # Proof object generating inferences   : 14
% 0.12/0.39  # Proof object simplifying inferences  : 25
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 9
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 21
% 0.12/0.39  # Removed in clause preprocessing      : 1
% 0.12/0.39  # Initial clauses in saturation        : 20
% 0.12/0.39  # Processed clauses                    : 66
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 3
% 0.12/0.39  # ...remaining for further processing  : 63
% 0.12/0.39  # Other redundant clauses eliminated   : 5
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 0
% 0.12/0.39  # Backward-rewritten                   : 9
% 0.12/0.39  # Generated clauses                    : 32
% 0.12/0.39  # ...of the previous two non-trivial   : 30
% 0.12/0.39  # Contextual simplify-reflections      : 1
% 0.12/0.39  # Paramodulations                      : 27
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 5
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 29
% 0.12/0.39  #    Positive orientable unit clauses  : 8
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 1
% 0.12/0.39  #    Non-unit-clauses                  : 20
% 0.12/0.39  # Current number of unprocessed clauses: 4
% 0.12/0.39  # ...number of literals in the above   : 18
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 30
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 218
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 42
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 4
% 0.12/0.39  # Unit Clause-clause subsumption calls : 9
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 3
% 0.12/0.39  # BW rewrite match successes           : 2
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 2637
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.056 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.060 s
% 0.12/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
