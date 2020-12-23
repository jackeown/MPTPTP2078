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
% DateTime   : Thu Dec  3 11:07:25 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 323 expanded)
%              Number of clauses        :   52 ( 134 expanded)
%              Number of leaves         :   18 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  229 (1390 expanded)
%              Number of equality atoms :   47 ( 119 expanded)
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

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t50_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | r1_tarski(X3,k8_relset_1(X1,X2,X4,k7_relset_1(X1,X2,X4,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t39_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1)) = k2_relset_1(X2,X1,X3)
        & k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = k1_relset_1(X2,X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

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

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | v1_relat_1(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_20,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_21,plain,(
    ! [X20,X21] : v1_relat_1(k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | r1_tarski(k9_relat_1(X26,k10_relat_1(X26,X25)),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k7_relset_1(X33,X34,X35,X36) = k9_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_27,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k8_relset_1(X37,X38,X39,X40) = k10_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_33,plain,(
    ! [X11,X12] :
      ( ~ r1_tarski(X11,X12)
      | k2_xboole_0(X11,X12) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_34,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_35,plain,(
    ! [X41,X42,X43] :
      ( ( k7_relset_1(X41,X42,X43,X41) = k2_relset_1(X41,X42,X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( k8_relset_1(X41,X42,X43,X42) = k1_relset_1(X41,X42,X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_36,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) = k7_relset_1(esk1_0,esk2_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_39,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ r1_tarski(X22,X23)
      | r1_tarski(k9_relat_1(X24,X22),k9_relat_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_45,plain,(
    ! [X47,X48,X49,X50] :
      ( ( X48 = k1_xboole_0
        | r1_tarski(X49,k8_relset_1(X47,X48,X50,k7_relset_1(X47,X48,X50,X49)))
        | ~ r1_tarski(X49,X47)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X47,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X47 != k1_xboole_0
        | r1_tarski(X49,k8_relset_1(X47,X48,X50,k7_relset_1(X47,X48,X50,X49)))
        | ~ r1_tarski(X49,X47)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X47,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_funct_2])])])).

fof(c_0_46,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_47,plain,(
    ! [X44,X45,X46] :
      ( ( k7_relset_1(X45,X44,X46,k8_relset_1(X45,X44,X46,X44)) = k2_relset_1(X45,X44,X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))) )
      & ( k8_relset_1(X45,X44,X46,k7_relset_1(X45,X44,X46,X45)) = k1_relset_1(X45,X44,X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).

cnf(c_0_48,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

fof(c_0_50,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk3_0,X1) = k8_relset_1(esk1_0,esk2_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_53,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) = esk5_0
    | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_55,plain,(
    ! [X8,X9,X10] :
      ( ~ r1_tarski(k2_xboole_0(X8,X9),X10)
      | r1_tarski(X8,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,k8_relset_1(X3,X1,X4,k7_relset_1(X3,X1,X4,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X3,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk3_0) = k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_24]),c_0_49])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X1)),X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) = esk5_0
    | r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_65,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ r1_tarski(X27,k1_relat_1(X29))
      | ~ r1_tarski(k9_relat_1(X29,X27),X28)
      | r1_tarski(X27,k10_relat_1(X29,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( k2_xboole_0(esk4_0,esk1_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,X1)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_24]),c_0_58]),c_0_29])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0)) = k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_24]),c_0_49]),c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k7_relset_1(esk1_0,esk2_0,esk3_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) = esk5_0
    | r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),k7_relset_1(esk1_0,esk2_0,esk3_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_30]),c_0_38]),c_0_38])).

cnf(c_0_73,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk1_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) = esk5_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_41])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,X2))
    | ~ r1_tarski(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0))
    | ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_61]),c_0_29]),c_0_30])]),c_0_52]),c_0_38])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)
    | ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_81]),c_0_83])).

cnf(c_0_86,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.45  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.21/0.45  # and selection function SelectNewComplexAHP.
% 0.21/0.45  #
% 0.21/0.45  # Preprocessing time       : 0.028 s
% 0.21/0.45  # Presaturation interreduction done
% 0.21/0.45  
% 0.21/0.45  # Proof found!
% 0.21/0.45  # SZS status Theorem
% 0.21/0.45  # SZS output start CNFRefutation
% 0.21/0.45  fof(t172_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 0.21/0.45  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.45  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.45  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.21/0.45  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.45  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.45  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.21/0.45  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.45  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 0.21/0.45  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.21/0.45  fof(t50_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r1_tarski(X3,k8_relset_1(X1,X2,X4,k7_relset_1(X1,X2,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_2)).
% 0.21/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.45  fof(t39_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1))=k2_relset_1(X2,X1,X3)&k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2))=k1_relset_1(X2,X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 0.21/0.45  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.21/0.45  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.21/0.45  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.21/0.45  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.45  fof(c_0_18, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(X1))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(X2))=>(r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)<=>r1_tarski(X4,k8_relset_1(X1,X2,X3,X5))))))))), inference(assume_negation,[status(cth)],[t172_funct_2])).
% 0.21/0.45  fof(c_0_19, plain, ![X18, X19]:(~v1_relat_1(X18)|(~m1_subset_1(X19,k1_zfmisc_1(X18))|v1_relat_1(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.45  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)))&(r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.21/0.45  fof(c_0_21, plain, ![X20, X21]:v1_relat_1(k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.45  fof(c_0_22, plain, ![X25, X26]:(~v1_relat_1(X26)|~v1_funct_1(X26)|r1_tarski(k9_relat_1(X26,k10_relat_1(X26,X25)),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.21/0.45  cnf(c_0_23, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.45  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_25, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.45  fof(c_0_26, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k7_relset_1(X33,X34,X35,X36)=k9_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.45  fof(c_0_27, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.45  cnf(c_0_28, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.45  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.21/0.45  cnf(c_0_31, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.45  fof(c_0_32, plain, ![X37, X38, X39, X40]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k8_relset_1(X37,X38,X39,X40)=k10_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.21/0.45  fof(c_0_33, plain, ![X11, X12]:(~r1_tarski(X11,X12)|k2_xboole_0(X11,X12)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.45  fof(c_0_34, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.45  fof(c_0_35, plain, ![X41, X42, X43]:((k7_relset_1(X41,X42,X43,X41)=k2_relset_1(X41,X42,X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(k8_relset_1(X41,X42,X43,X42)=k1_relset_1(X41,X42,X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.21/0.45  cnf(c_0_36, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.45  cnf(c_0_37, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.21/0.45  cnf(c_0_38, negated_conjecture, (k9_relat_1(esk3_0,X1)=k7_relset_1(esk1_0,esk2_0,esk3_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.21/0.45  cnf(c_0_39, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.21/0.45  fof(c_0_40, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|(~r1_tarski(X22,X23)|r1_tarski(k9_relat_1(X24,X22),k9_relat_1(X24,X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.21/0.45  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.45  cnf(c_0_42, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_43, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.45  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  fof(c_0_45, plain, ![X47, X48, X49, X50]:((X48=k1_xboole_0|r1_tarski(X49,k8_relset_1(X47,X48,X50,k7_relset_1(X47,X48,X50,X49)))|~r1_tarski(X49,X47)|(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(X47!=k1_xboole_0|r1_tarski(X49,k8_relset_1(X47,X48,X50,k7_relset_1(X47,X48,X50,X49)))|~r1_tarski(X49,X47)|(~v1_funct_1(X50)|~v1_funct_2(X50,X47,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_funct_2])])])).
% 0.21/0.45  fof(c_0_46, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.45  fof(c_0_47, plain, ![X44, X45, X46]:((k7_relset_1(X45,X44,X46,k8_relset_1(X45,X44,X46,X44))=k2_relset_1(X45,X44,X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))&(k8_relset_1(X45,X44,X46,k7_relset_1(X45,X44,X46,X45))=k1_relset_1(X45,X44,X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X44))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).
% 0.21/0.45  cnf(c_0_48, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.45  cnf(c_0_49, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_24])).
% 0.21/0.45  fof(c_0_50, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.21/0.45  cnf(c_0_51, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.45  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk3_0,X1)=k8_relset_1(esk1_0,esk2_0,esk3_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 0.21/0.45  cnf(c_0_53, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.45  cnf(c_0_54, negated_conjecture, (k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)=esk5_0|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.45  fof(c_0_55, plain, ![X8, X9, X10]:(~r1_tarski(k2_xboole_0(X8,X9),X10)|r1_tarski(X8,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.21/0.45  cnf(c_0_56, negated_conjecture, (r1_tarski(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.45  cnf(c_0_57, plain, (X1=k1_xboole_0|r1_tarski(X2,k8_relset_1(X3,X1,X4,k7_relset_1(X3,X1,X4,X2)))|~r1_tarski(X2,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X3,X1)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.45  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_59, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.45  cnf(c_0_60, plain, (k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.45  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk3_0)=k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_24]), c_0_49])).
% 0.21/0.45  cnf(c_0_62, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.45  cnf(c_0_63, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X1)),X1)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.45  cnf(c_0_64, negated_conjecture, (k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)=esk5_0|r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.45  fof(c_0_65, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|(~r1_tarski(X27,k1_relat_1(X29))|~r1_tarski(k9_relat_1(X29,X27),X28)|r1_tarski(X27,k10_relat_1(X29,X28)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.21/0.45  cnf(c_0_66, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.45  cnf(c_0_67, negated_conjecture, (k2_xboole_0(esk4_0,esk1_0)=esk1_0), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 0.21/0.45  cnf(c_0_68, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,X1)))|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_24]), c_0_58]), c_0_29])])).
% 0.21/0.45  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_59])).
% 0.21/0.45  cnf(c_0_70, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0))=k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_24]), c_0_49]), c_0_61])).
% 0.21/0.45  cnf(c_0_71, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k7_relset_1(esk1_0,esk2_0,esk3_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X2)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.45  cnf(c_0_72, negated_conjecture, (k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)=esk5_0|r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),k7_relset_1(esk1_0,esk2_0,esk3_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_30]), c_0_38]), c_0_38])).
% 0.21/0.45  cnf(c_0_73, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.45  cnf(c_0_74, negated_conjecture, (r1_tarski(esk4_0,X1)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.21/0.45  cnf(c_0_75, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk1_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.21/0.45  cnf(c_0_76, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_66, c_0_69])).
% 0.21/0.45  cnf(c_0_77, negated_conjecture, (k2_xboole_0(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)=esk5_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_41])).
% 0.21/0.45  cnf(c_0_78, negated_conjecture, (r1_tarski(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,X2))|~r1_tarski(X1,k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0))|~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_61]), c_0_29]), c_0_30])]), c_0_52]), c_0_38])).
% 0.21/0.45  cnf(c_0_79, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.21/0.45  cnf(c_0_80, negated_conjecture, (~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_81, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.45  cnf(c_0_82, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,X1))|~r1_tarski(k7_relset_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.45  cnf(c_0_83, negated_conjecture, (~r1_tarski(esk4_0,k8_relset_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.21/0.45  cnf(c_0_84, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.45  cnf(c_0_85, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_81]), c_0_83])).
% 0.21/0.45  cnf(c_0_86, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.45  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_86])]), ['proof']).
% 0.21/0.45  # SZS output end CNFRefutation
% 0.21/0.45  # Proof object total steps             : 88
% 0.21/0.45  # Proof object clause steps            : 52
% 0.21/0.45  # Proof object formula steps           : 36
% 0.21/0.45  # Proof object conjectures             : 36
% 0.21/0.45  # Proof object clause conjectures      : 33
% 0.21/0.45  # Proof object formula conjectures     : 3
% 0.21/0.45  # Proof object initial clauses used    : 24
% 0.21/0.45  # Proof object initial formulas used   : 18
% 0.21/0.45  # Proof object generating inferences   : 23
% 0.21/0.45  # Proof object simplifying inferences  : 28
% 0.21/0.45  # Training examples: 0 positive, 0 negative
% 0.21/0.45  # Parsed axioms                        : 18
% 0.21/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.45  # Initial clauses                      : 32
% 0.21/0.45  # Removed in clause preprocessing      : 0
% 0.21/0.45  # Initial clauses in saturation        : 32
% 0.21/0.45  # Processed clauses                    : 796
% 0.21/0.45  # ...of these trivial                  : 38
% 0.21/0.45  # ...subsumed                          : 271
% 0.21/0.45  # ...remaining for further processing  : 487
% 0.21/0.45  # Other redundant clauses eliminated   : 3
% 0.21/0.45  # Clauses deleted for lack of memory   : 0
% 0.21/0.45  # Backward-subsumed                    : 31
% 0.21/0.45  # Backward-rewritten                   : 334
% 0.21/0.45  # Generated clauses                    : 2006
% 0.21/0.45  # ...of the previous two non-trivial   : 1898
% 0.21/0.45  # Contextual simplify-reflections      : 1
% 0.21/0.45  # Paramodulations                      : 1994
% 0.21/0.45  # Factorizations                       : 0
% 0.21/0.45  # Equation resolutions                 : 3
% 0.21/0.45  # Propositional unsat checks           : 0
% 0.21/0.45  #    Propositional check models        : 0
% 0.21/0.45  #    Propositional check unsatisfiable : 0
% 0.21/0.45  #    Propositional clauses             : 0
% 0.21/0.45  #    Propositional clauses after purity: 0
% 0.21/0.45  #    Propositional unsat core size     : 0
% 0.21/0.45  #    Propositional preprocessing time  : 0.000
% 0.21/0.45  #    Propositional encoding time       : 0.000
% 0.21/0.45  #    Propositional solver time         : 0.000
% 0.21/0.45  #    Success case prop preproc time    : 0.000
% 0.21/0.45  #    Success case prop encoding time   : 0.000
% 0.21/0.45  #    Success case prop solver time     : 0.000
% 0.21/0.45  # Current number of processed clauses  : 79
% 0.21/0.45  #    Positive orientable unit clauses  : 27
% 0.21/0.45  #    Positive unorientable unit clauses: 4
% 0.21/0.45  #    Negative unit clauses             : 1
% 0.21/0.45  #    Non-unit-clauses                  : 47
% 0.21/0.45  # Current number of unprocessed clauses: 854
% 0.21/0.45  # ...number of literals in the above   : 1401
% 0.21/0.45  # Current number of archived formulas  : 0
% 0.21/0.45  # Current number of archived clauses   : 405
% 0.21/0.45  # Clause-clause subsumption calls (NU) : 13763
% 0.21/0.45  # Rec. Clause-clause subsumption calls : 12824
% 0.21/0.45  # Non-unit clause-clause subsumptions  : 289
% 0.21/0.45  # Unit Clause-clause subsumption calls : 1559
% 0.21/0.45  # Rewrite failures with RHS unbound    : 0
% 0.21/0.45  # BW rewrite match attempts            : 721
% 0.21/0.45  # BW rewrite match successes           : 23
% 0.21/0.45  # Condensation attempts                : 0
% 0.21/0.45  # Condensation successes               : 0
% 0.21/0.45  # Termbank termtop insertions          : 40137
% 0.21/0.45  
% 0.21/0.45  # -------------------------------------------------
% 0.21/0.45  # User time                : 0.103 s
% 0.21/0.45  # System time              : 0.006 s
% 0.21/0.45  # Total time               : 0.109 s
% 0.21/0.45  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
