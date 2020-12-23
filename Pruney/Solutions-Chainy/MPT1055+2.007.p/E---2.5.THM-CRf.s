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
% DateTime   : Thu Dec  3 11:07:24 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 217 expanded)
%              Number of clauses        :   45 (  92 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 (1001 expanded)
%              Number of equality atoms :   33 (  53 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t48_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & ( ~ r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)
      | ~ r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0)) )
    & ( r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)
      | r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X40,X41,X42] :
      ( ( X41 = k1_xboole_0
        | k8_relset_1(X40,X41,X42,X41) = X40
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_xboole_0
        | k8_relset_1(X40,X41,X42,X41) = X40
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).

fof(c_0_18,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k8_relset_1(X36,X37,X38,X39) = k10_relat_1(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k10_relat_1(X23,X22),k1_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_20,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,X1) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k7_relset_1(X32,X33,X34,X35) = k9_relat_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( k8_relset_1(esk2_0,esk3_0,esk4_0,esk3_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_23]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k8_relset_1(esk2_0,esk3_0,esk4_0,X1) = k10_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

fof(c_0_31,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | r1_tarski(X11,X9)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r1_tarski(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k1_zfmisc_1(X9) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | ~ r1_tarski(esk1_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | r1_tarski(esk1_2(X13,X14),X13)
        | X14 = k1_zfmisc_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_33,plain,(
    ! [X16] : ~ v1_xboole_0(k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_34,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk4_0,esk3_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)
    | r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( k7_relset_1(esk2_0,esk3_0,esk4_0,X1) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

fof(c_0_44,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk2_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

fof(c_0_49,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(k9_relat_1(X21,X19),k9_relat_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0))
    | r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_52,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ r1_tarski(X26,k1_relat_1(X28))
      | ~ r1_tarski(k9_relat_1(X28,X26),X27)
      | r1_tarski(X26,k10_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_53,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(X1,k1_relat_1(esk4_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk5_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)
    | r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_30])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_24])])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk5_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk4_0,esk6_0)))
    | r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_43])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk5_0,k10_relat_1(esk4_0,X1))
    | ~ r1_tarski(k9_relat_1(esk4_0,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_24]),c_0_28])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_28]),c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0))
    | ~ r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_65])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:43:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.51  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.21/0.51  # and selection function SelectNewComplexAHP.
% 0.21/0.51  #
% 0.21/0.51  # Preprocessing time       : 0.028 s
% 0.21/0.51  # Presaturation interreduction done
% 0.21/0.51  
% 0.21/0.51  # Proof found!
% 0.21/0.51  # SZS status Theorem
% 0.21/0.51  # SZS output start CNFRefutation
% 0.21/0.51  fof(t172_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 0.21/0.51  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.51  fof(t48_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 0.21/0.51  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.21/0.51  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.21/0.51  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.51  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.21/0.51  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.51  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.21/0.51  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.21/0.51  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.21/0.51  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.21/0.51  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.21/0.51  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.51  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t172_funct_2])).
% 0.21/0.51  fof(c_0_15, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.51  fof(c_0_16, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))&((~r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)|~r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0)))&(r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)|r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.21/0.51  fof(c_0_17, plain, ![X40, X41, X42]:((X41=k1_xboole_0|k8_relset_1(X40,X41,X42,X41)=X40|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&(X40!=k1_xboole_0|k8_relset_1(X40,X41,X42,X41)=X40|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).
% 0.21/0.51  fof(c_0_18, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k8_relset_1(X36,X37,X38,X39)=k10_relat_1(X38,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.21/0.51  fof(c_0_19, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k10_relat_1(X23,X22),k1_relat_1(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.21/0.51  cnf(c_0_20, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.51  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_22, plain, (X1=k1_xboole_0|k8_relset_1(X2,X1,X3,X1)=X2|~v1_funct_1(X3)|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.51  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_25, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.51  fof(c_0_26, plain, ![X32, X33, X34, X35]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k7_relset_1(X32,X33,X34,X35)=k9_relat_1(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.51  cnf(c_0_27, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.21/0.51  cnf(c_0_29, negated_conjecture, (k8_relset_1(esk2_0,esk3_0,esk4_0,esk3_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_21]), c_0_23]), c_0_24])])).
% 0.21/0.51  cnf(c_0_30, negated_conjecture, (k8_relset_1(esk2_0,esk3_0,esk4_0,X1)=k10_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 0.21/0.51  fof(c_0_31, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X11,X10)|r1_tarski(X11,X9)|X10!=k1_zfmisc_1(X9))&(~r1_tarski(X12,X9)|r2_hidden(X12,X10)|X10!=k1_zfmisc_1(X9)))&((~r2_hidden(esk1_2(X13,X14),X14)|~r1_tarski(esk1_2(X13,X14),X13)|X14=k1_zfmisc_1(X13))&(r2_hidden(esk1_2(X13,X14),X14)|r1_tarski(esk1_2(X13,X14),X13)|X14=k1_zfmisc_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.21/0.51  fof(c_0_32, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.51  fof(c_0_33, plain, ![X16]:~v1_xboole_0(k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.21/0.51  cnf(c_0_34, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.51  fof(c_0_35, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.21/0.51  cnf(c_0_36, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.51  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk4_0,esk3_0)=esk2_0|esk3_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.51  cnf(c_0_38, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.51  cnf(c_0_39, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.51  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_41, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.51  cnf(c_0_42, negated_conjecture, (r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)|r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_43, negated_conjecture, (k7_relset_1(esk2_0,esk3_0,esk4_0,X1)=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.21/0.51  fof(c_0_44, plain, ![X24, X25]:(~v1_relat_1(X25)|~v1_funct_1(X25)|r1_tarski(k9_relat_1(X25,k10_relat_1(X25,X24)),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.21/0.51  cnf(c_0_45, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.51  cnf(c_0_46, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk2_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.51  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_38])).
% 0.21/0.51  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.21/0.51  fof(c_0_49, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(X19,X20)|r1_tarski(k9_relat_1(X21,X19),k9_relat_1(X21,X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.21/0.51  cnf(c_0_50, negated_conjecture, (r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0))|r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.51  cnf(c_0_51, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.51  fof(c_0_52, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~r1_tarski(X26,k1_relat_1(X28))|~r1_tarski(k9_relat_1(X28,X26),X27)|r1_tarski(X26,k10_relat_1(X28,X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.21/0.51  cnf(c_0_53, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(X1,k1_relat_1(esk4_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.51  cnf(c_0_54, negated_conjecture, (r1_tarski(esk5_0,esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.51  cnf(c_0_55, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.51  cnf(c_0_56, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)|r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0))), inference(rw,[status(thm)],[c_0_50, c_0_30])).
% 0.21/0.51  cnf(c_0_57, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_28]), c_0_24])])).
% 0.21/0.51  cnf(c_0_58, negated_conjecture, (~r1_tarski(k7_relset_1(esk2_0,esk3_0,esk4_0,esk5_0),esk6_0)|~r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_59, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.21/0.51  cnf(c_0_60, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk5_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.51  cnf(c_0_61, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk5_0),k9_relat_1(X1,k10_relat_1(esk4_0,esk6_0)))|r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.21/0.51  cnf(c_0_62, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk4_0,k10_relat_1(esk4_0,X2)))), inference(spm,[status(thm)],[c_0_45, c_0_57])).
% 0.21/0.51  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk5_0,k8_relset_1(esk2_0,esk3_0,esk4_0,esk6_0))|~r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_58, c_0_43])).
% 0.21/0.51  cnf(c_0_64, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk5_0,k10_relat_1(esk4_0,X1))|~r1_tarski(k9_relat_1(esk4_0,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_24]), c_0_28])])).
% 0.21/0.51  cnf(c_0_65, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_28]), c_0_62])).
% 0.21/0.51  cnf(c_0_66, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0))|~r1_tarski(k9_relat_1(esk4_0,esk5_0),esk6_0)), inference(rw,[status(thm)],[c_0_63, c_0_30])).
% 0.21/0.51  cnf(c_0_67, negated_conjecture, (esk3_0=k1_xboole_0|r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.51  cnf(c_0_68, negated_conjecture, (~r1_tarski(esk5_0,k10_relat_1(esk4_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_65])])).
% 0.21/0.51  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.51  cnf(c_0_71, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.51  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), ['proof']).
% 0.21/0.51  # SZS output end CNFRefutation
% 0.21/0.51  # Proof object total steps             : 73
% 0.21/0.51  # Proof object clause steps            : 45
% 0.21/0.51  # Proof object formula steps           : 28
% 0.21/0.51  # Proof object conjectures             : 34
% 0.21/0.51  # Proof object clause conjectures      : 31
% 0.21/0.51  # Proof object formula conjectures     : 3
% 0.21/0.51  # Proof object initial clauses used    : 20
% 0.21/0.51  # Proof object initial formulas used   : 14
% 0.21/0.51  # Proof object generating inferences   : 16
% 0.21/0.51  # Proof object simplifying inferences  : 22
% 0.21/0.51  # Training examples: 0 positive, 0 negative
% 0.21/0.51  # Parsed axioms                        : 14
% 0.21/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.51  # Initial clauses                      : 26
% 0.21/0.51  # Removed in clause preprocessing      : 0
% 0.21/0.51  # Initial clauses in saturation        : 26
% 0.21/0.51  # Processed clauses                    : 812
% 0.21/0.51  # ...of these trivial                  : 3
% 0.21/0.51  # ...subsumed                          : 205
% 0.21/0.51  # ...remaining for further processing  : 604
% 0.21/0.51  # Other redundant clauses eliminated   : 3
% 0.21/0.51  # Clauses deleted for lack of memory   : 0
% 0.21/0.51  # Backward-subsumed                    : 20
% 0.21/0.51  # Backward-rewritten                   : 412
% 0.21/0.51  # Generated clauses                    : 5906
% 0.21/0.51  # ...of the previous two non-trivial   : 5966
% 0.21/0.51  # Contextual simplify-reflections      : 2
% 0.21/0.51  # Paramodulations                      : 5828
% 0.21/0.51  # Factorizations                       : 70
% 0.21/0.51  # Equation resolutions                 : 3
% 0.21/0.51  # Propositional unsat checks           : 0
% 0.21/0.51  #    Propositional check models        : 0
% 0.21/0.51  #    Propositional check unsatisfiable : 0
% 0.21/0.51  #    Propositional clauses             : 0
% 0.21/0.51  #    Propositional clauses after purity: 0
% 0.21/0.51  #    Propositional unsat core size     : 0
% 0.21/0.51  #    Propositional preprocessing time  : 0.000
% 0.21/0.51  #    Propositional encoding time       : 0.000
% 0.21/0.51  #    Propositional solver time         : 0.000
% 0.21/0.51  #    Success case prop preproc time    : 0.000
% 0.21/0.51  #    Success case prop encoding time   : 0.000
% 0.21/0.51  #    Success case prop solver time     : 0.000
% 0.21/0.51  # Current number of processed clauses  : 138
% 0.21/0.51  #    Positive orientable unit clauses  : 34
% 0.21/0.51  #    Positive unorientable unit clauses: 0
% 0.21/0.51  #    Negative unit clauses             : 3
% 0.21/0.51  #    Non-unit-clauses                  : 101
% 0.21/0.51  # Current number of unprocessed clauses: 5025
% 0.21/0.51  # ...number of literals in the above   : 20147
% 0.21/0.51  # Current number of archived formulas  : 0
% 0.21/0.51  # Current number of archived clauses   : 463
% 0.21/0.51  # Clause-clause subsumption calls (NU) : 11716
% 0.21/0.51  # Rec. Clause-clause subsumption calls : 6340
% 0.21/0.51  # Non-unit clause-clause subsumptions  : 219
% 0.21/0.51  # Unit Clause-clause subsumption calls : 896
% 0.21/0.51  # Rewrite failures with RHS unbound    : 0
% 0.21/0.51  # BW rewrite match attempts            : 73
% 0.21/0.51  # BW rewrite match successes           : 16
% 0.21/0.51  # Condensation attempts                : 0
% 0.21/0.51  # Condensation successes               : 0
% 0.21/0.51  # Termbank termtop insertions          : 133112
% 0.21/0.51  
% 0.21/0.51  # -------------------------------------------------
% 0.21/0.51  # User time                : 0.155 s
% 0.21/0.51  # System time              : 0.011 s
% 0.21/0.51  # Total time               : 0.166 s
% 0.21/0.51  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
