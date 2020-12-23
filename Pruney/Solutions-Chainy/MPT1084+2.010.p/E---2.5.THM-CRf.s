%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:24 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 180 expanded)
%              Number of clauses        :   34 (  70 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  222 ( 926 expanded)
%              Number of equality atoms :   79 ( 238 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
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

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X31] :
      ( ~ v1_xboole_0(esk2_0)
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,esk2_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
      & ( ~ m1_subset_1(X31,esk2_0)
        | k3_funct_2(esk2_0,esk2_0,esk3_0,X31) = X31 )
      & ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

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

fof(c_0_14,plain,(
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

cnf(c_0_15,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk3_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k1_relset_1(esk2_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X20,X21,X22,X23] :
      ( v1_xboole_0(X20)
      | ~ v1_funct_1(X22)
      | ~ v1_funct_2(X22,X20,X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | ~ m1_subset_1(X23,X20)
      | k3_funct_2(X20,X21,X22,X23) = k1_funct_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_24,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | m1_subset_1(X5,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_25,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk2_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_16])])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | esk2_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

fof(c_0_32,plain,(
    ! [X25,X26,X27,X28] :
      ( ( ~ r2_funct_2(X25,X26,X27,X28)
        | X27 = X28
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( X27 != X28
        | r2_funct_2(X25,X26,X27,X28)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X25,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X25,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_33,negated_conjecture,
    ( k3_funct_2(X1,X2,esk3_0,X3) = k1_funct_1(esk3_0,X3)
    | v1_xboole_0(X1)
    | ~ v1_funct_2(esk3_0,X1,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | esk2_0 = k1_xboole_0
    | m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk1_2(X2,X1)) != esk1_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_37,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X24] : k6_partfun1(X24) = k6_relat_1(X24) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_39,negated_conjecture,
    ( k3_funct_2(esk2_0,X1,esk3_0,esk1_2(esk2_0,esk3_0)) = k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))
    | k6_relat_1(esk2_0) = esk3_0
    | esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,esk2_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1)) != esk1_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,X1) = X1
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k3_funct_2(esk2_0,esk2_0,esk3_0,esk1_2(esk2_0,esk3_0)) = k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))
    | k6_relat_1(esk2_0) = esk3_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | esk2_0 = k1_xboole_0
    | k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0)) != esk1_2(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_47,negated_conjecture,
    ( r2_funct_2(X1,X2,esk3_0,esk3_0)
    | ~ v1_funct_2(esk3_0,X1,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k6_relat_1(esk2_0) = esk3_0
    | esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_20]),c_0_16])])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_51]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n016.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:11:19 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.18/0.36  # and selection function HSelectMinInfpos.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.029 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t201_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 0.18/0.36  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.36  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.18/0.36  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.18/0.36  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.36  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.18/0.36  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.18/0.36  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.18/0.36  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.18/0.36  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.36  fof(c_0_10, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(![X3]:(m1_subset_1(X3,X1)=>k3_funct_2(X1,X1,X2,X3)=X3)=>r2_funct_2(X1,X1,X2,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t201_funct_2])).
% 0.18/0.36  fof(c_0_11, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k1_relset_1(X14,X15,X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.36  fof(c_0_12, negated_conjecture, ![X31]:(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk2_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))))&((~m1_subset_1(X31,esk2_0)|k3_funct_2(esk2_0,esk2_0,esk3_0,X31)=X31)&~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.18/0.36  fof(c_0_13, plain, ![X7, X8, X9]:(((k1_relat_1(X8)=X7|X8!=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(~r2_hidden(X9,X7)|k1_funct_1(X8,X9)=X9|X8!=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&((r2_hidden(esk1_2(X7,X8),X7)|k1_relat_1(X8)!=X7|X8=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(k1_funct_1(X8,esk1_2(X7,X8))!=esk1_2(X7,X8)|k1_relat_1(X8)!=X7|X8=k6_relat_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.18/0.36  fof(c_0_14, plain, ![X17, X18, X19]:((((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&((~v1_funct_2(X19,X17,X18)|X19=k1_xboole_0|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X19!=k1_xboole_0|v1_funct_2(X19,X17,X18)|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.18/0.36  cnf(c_0_15, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.36  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  fof(c_0_17, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.36  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_19, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.36  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk3_0,esk2_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (k1_relset_1(esk2_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.36  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.36  fof(c_0_23, plain, ![X20, X21, X22, X23]:(v1_xboole_0(X20)|~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~m1_subset_1(X23,X20)|k3_funct_2(X20,X21,X22,X23)=k1_funct_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.18/0.36  fof(c_0_24, plain, ![X5, X6]:(~r2_hidden(X5,X6)|m1_subset_1(X5,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.18/0.36  cnf(c_0_25, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_18])).
% 0.18/0.36  cnf(c_0_26, negated_conjecture, (k1_relat_1(esk3_0)=esk2_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_16])])).
% 0.18/0.36  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_16])).
% 0.18/0.36  cnf(c_0_29, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.36  cnf(c_0_30, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_31, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|esk2_0=k1_xboole_0|r2_hidden(esk1_2(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.18/0.36  fof(c_0_32, plain, ![X25, X26, X27, X28]:((~r2_funct_2(X25,X26,X27,X28)|X27=X28|(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&(X27!=X28|r2_funct_2(X25,X26,X27,X28)|(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|~v1_funct_1(X28)|~v1_funct_2(X28,X25,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, (k3_funct_2(X1,X2,esk3_0,X3)=k1_funct_1(esk3_0,X3)|v1_xboole_0(X1)|~v1_funct_2(esk3_0,X1,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,X1)), inference(spm,[status(thm)],[c_0_29, c_0_27])).
% 0.18/0.36  cnf(c_0_34, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|esk2_0=k1_xboole_0|m1_subset_1(esk1_2(esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.18/0.36  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_36, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk1_2(X2,X1))!=esk1_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  cnf(c_0_37, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.36  fof(c_0_38, plain, ![X24]:k6_partfun1(X24)=k6_relat_1(X24), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (k3_funct_2(esk2_0,X1,esk3_0,esk1_2(esk2_0,esk3_0))=k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))|k6_relat_1(esk2_0)=esk3_0|esk2_0=k1_xboole_0|~v1_funct_2(esk3_0,esk2_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.18/0.36  cnf(c_0_40, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk1_2(k1_relat_1(X1),X1))!=esk1_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_36])).
% 0.18/0.36  cnf(c_0_41, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_37])).
% 0.18/0.36  cnf(c_0_42, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_partfun1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_43, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,X1)=X1|~m1_subset_1(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, (k3_funct_2(esk2_0,esk2_0,esk3_0,esk1_2(esk2_0,esk3_0))=k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))|k6_relat_1(esk2_0)=esk3_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_16])])).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|esk2_0=k1_xboole_0|k1_funct_1(esk3_0,esk1_2(esk2_0,esk3_0))!=esk1_2(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_26]), c_0_27]), c_0_28])])).
% 0.18/0.36  cnf(c_0_47, negated_conjecture, (r2_funct_2(X1,X2,esk3_0,esk3_0)|~v1_funct_2(esk3_0,X1,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.18/0.36  cnf(c_0_48, negated_conjecture, (~r2_funct_2(esk2_0,esk2_0,esk3_0,k6_relat_1(esk2_0))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.36  cnf(c_0_49, negated_conjecture, (k6_relat_1(esk2_0)=esk3_0|esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_34]), c_0_46])).
% 0.18/0.36  cnf(c_0_50, negated_conjecture, (r2_funct_2(esk2_0,esk2_0,esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_20]), c_0_16])])).
% 0.18/0.36  cnf(c_0_51, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.18/0.36  cnf(c_0_52, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.36  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_51]), c_0_52])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 54
% 0.18/0.36  # Proof object clause steps            : 34
% 0.18/0.36  # Proof object formula steps           : 20
% 0.18/0.36  # Proof object conjectures             : 24
% 0.18/0.36  # Proof object clause conjectures      : 21
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 16
% 0.18/0.36  # Proof object initial formulas used   : 10
% 0.18/0.36  # Proof object generating inferences   : 13
% 0.18/0.36  # Proof object simplifying inferences  : 25
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 10
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 24
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 23
% 0.18/0.36  # Processed clauses                    : 80
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 7
% 0.18/0.36  # ...remaining for further processing  : 73
% 0.18/0.36  # Other redundant clauses eliminated   : 12
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 7
% 0.18/0.36  # Backward-rewritten                   : 9
% 0.18/0.36  # Generated clauses                    : 48
% 0.18/0.36  # ...of the previous two non-trivial   : 45
% 0.18/0.36  # Contextual simplify-reflections      : 2
% 0.18/0.36  # Paramodulations                      : 29
% 0.18/0.36  # Factorizations                       : 8
% 0.18/0.36  # Equation resolutions                 : 12
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 25
% 0.18/0.36  #    Positive orientable unit clauses  : 4
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 0
% 0.18/0.36  #    Non-unit-clauses                  : 21
% 0.18/0.36  # Current number of unprocessed clauses: 7
% 0.18/0.36  # ...number of literals in the above   : 25
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 40
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 276
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 93
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 16
% 0.18/0.36  # Unit Clause-clause subsumption calls : 3
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 2
% 0.18/0.36  # BW rewrite match successes           : 1
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 2868
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.033 s
% 0.18/0.36  # System time              : 0.004 s
% 0.18/0.36  # Total time               : 0.037 s
% 0.18/0.36  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
