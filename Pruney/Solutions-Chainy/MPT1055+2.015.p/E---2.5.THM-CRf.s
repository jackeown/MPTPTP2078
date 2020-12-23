%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:25 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 211 expanded)
%              Number of clauses        :   41 (  88 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  212 ( 979 expanded)
%              Number of equality atoms :   42 (  63 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t172_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,k1_zfmisc_1(X2))
                     => ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
                      <=> r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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

fof(t158_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,X1,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(X2))
                       => ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
                        <=> r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t172_funct_2])).

fof(c_0_15,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k7_relset_1(X29,X30,X31,X32) = k9_relat_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
      | ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) )
    & ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
      | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_17,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k8_relset_1(X33,X34,X35,X36) = k10_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k7_relset_1(esk1_0,esk2_0,esk3_0,X1) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(k9_relat_1(X19,X17),k9_relat_1(X20,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,X1) = k10_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

fof(c_0_28,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | r1_tarski(k9_relat_1(X22,k10_relat_1(X22,X21)),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_30,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)
    | r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(X8,X9)
      | ~ r1_tarski(X9,X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_31])])).

fof(c_0_39,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k1_relset_1(X26,X27,X28) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X2,k10_relat_1(esk3_0,esk5_0)))
    | r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

fof(c_0_45,plain,(
    ! [X23,X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ r1_tarski(X23,k1_relat_1(X25))
      | ~ r1_tarski(k9_relat_1(X25,X23),X24)
      | r1_tarski(X23,k10_relat_1(X25,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_46,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_21])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k10_relat_1(esk3_0,esk5_0)))
    | r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relset_1(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_38]),c_0_49])).

fof(c_0_54,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X39 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != k1_xboole_0
        | v1_funct_2(X39,X37,X38)
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_55,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk3_0,X2))
    | ~ r1_tarski(X1,k1_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ r1_tarski(k9_relat_1(esk3_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_37]),c_0_38])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_58,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_18]),c_0_59])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 10:12:11 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.41  # and selection function SelectNewComplexAHP.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.030 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t172_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 0.20/0.41  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.20/0.41  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.20/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.41  fof(t158_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.20/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.41  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.20/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t172_funct_2])).
% 0.20/0.41  fof(c_0_15, plain, ![X29, X30, X31, X32]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k7_relset_1(X29,X30,X31,X32)=k9_relat_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.20/0.41  fof(c_0_16, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)))&(r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.20/0.41  cnf(c_0_17, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  fof(c_0_19, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k8_relset_1(X33,X34,X35,X36)=k10_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (k7_relset_1(esk1_0,esk2_0,esk3_0,X1)=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.41  cnf(c_0_22, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.41  fof(c_0_23, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.41  fof(c_0_24, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.41  fof(c_0_25, plain, ![X17, X18, X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|(~r1_tarski(X19,X20)|~r1_tarski(X17,X18)|r1_tarski(k9_relat_1(X19,X17),k9_relat_1(X20,X18))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_relat_1])])])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))|r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,X1)=k10_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.20/0.41  fof(c_0_28, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_29, plain, ![X21, X22]:(~v1_relat_1(X22)|~v1_funct_1(X22)|r1_tarski(k9_relat_1(X22,k10_relat_1(X22,X21)),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.41  cnf(c_0_30, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_32, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.41  fof(c_0_35, plain, ![X8, X9, X10]:(~r1_tarski(X8,X9)|~r1_tarski(X9,X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.20/0.41  cnf(c_0_36, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_31])])).
% 0.20/0.41  fof(c_0_39, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k1_relset_1(X26,X27,X28)=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X2,k10_relat_1(esk3_0,esk5_0)))|r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.41  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.41  fof(c_0_45, plain, ![X23, X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|(~r1_tarski(X23,k1_relat_1(X25))|~r1_tarski(k9_relat_1(X25,X23),X24)|r1_tarski(X23,k10_relat_1(X25,X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.20/0.41  cnf(c_0_46, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))|~r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_40, c_0_21])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k10_relat_1(esk3_0,esk5_0)))|r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.41  cnf(c_0_50, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk3_0)=k1_relset_1(esk1_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_18])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (~r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))|~r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(rw,[status(thm)],[c_0_47, c_0_27])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,esk4_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_38]), c_0_49])).
% 0.20/0.41  fof(c_0_54, plain, ![X37, X38, X39]:((((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))&((~v1_funct_2(X39,X37,X38)|X39=k1_xboole_0|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X39!=k1_xboole_0|v1_funct_2(X39,X37,X38)|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.41  fof(c_0_55, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,k10_relat_1(esk3_0,X2))|~r1_tarski(X1,k1_relset_1(esk1_0,esk2_0,esk3_0))|~r1_tarski(k9_relat_1(esk3_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_37]), c_0_38])])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk4_0,k10_relat_1(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.20/0.41  cnf(c_0_58, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_60, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk4_0,k1_relset_1(esk1_0,esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_57])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_18]), c_0_59])])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (r1_tarski(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.20/0.41  cnf(c_0_67, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_67])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 69
% 0.20/0.41  # Proof object clause steps            : 41
% 0.20/0.41  # Proof object formula steps           : 28
% 0.20/0.41  # Proof object conjectures             : 30
% 0.20/0.41  # Proof object clause conjectures      : 27
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 20
% 0.20/0.41  # Proof object initial formulas used   : 14
% 0.20/0.41  # Proof object generating inferences   : 14
% 0.20/0.41  # Proof object simplifying inferences  : 23
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 14
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 30
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 30
% 0.20/0.41  # Processed clauses                    : 370
% 0.20/0.41  # ...of these trivial                  : 6
% 0.20/0.41  # ...subsumed                          : 32
% 0.20/0.41  # ...remaining for further processing  : 332
% 0.20/0.41  # Other redundant clauses eliminated   : 7
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 3
% 0.20/0.41  # Backward-rewritten                   : 198
% 0.20/0.41  # Generated clauses                    : 983
% 0.20/0.41  # ...of the previous two non-trivial   : 1050
% 0.20/0.41  # Contextual simplify-reflections      : 32
% 0.20/0.41  # Paramodulations                      : 974
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 7
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 93
% 0.20/0.41  #    Positive orientable unit clauses  : 27
% 0.20/0.41  #    Positive unorientable unit clauses: 1
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 63
% 0.20/0.41  # Current number of unprocessed clauses: 611
% 0.20/0.41  # ...number of literals in the above   : 1799
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 233
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 2701
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 2013
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 67
% 0.20/0.41  # Unit Clause-clause subsumption calls : 394
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 65
% 0.20/0.41  # BW rewrite match successes           : 5
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 25957
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.062 s
% 0.20/0.41  # System time              : 0.009 s
% 0.20/0.41  # Total time               : 0.071 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
