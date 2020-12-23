%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:24 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 416 expanded)
%              Number of clauses        :   69 ( 182 expanded)
%              Number of leaves         :   21 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          :  320 (1560 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t29_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t26_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | v2_funct_1(X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(c_0_21,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X19,X20] :
      ( ~ v1_xboole_0(X19)
      | v1_xboole_0(k2_zfmisc_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

fof(c_0_26,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_30,plain,(
    ! [X48] :
      ( v1_partfun1(k6_partfun1(X48),X48)
      & m1_subset_1(k6_partfun1(X48),k1_zfmisc_1(k2_zfmisc_1(X48,X48))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_31,plain,(
    ! [X55] : k6_partfun1(X55) = k6_relat_1(X55) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_35,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_28])).

fof(c_0_39,plain,(
    ! [X21,X22] :
      ( ~ v1_xboole_0(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | v1_xboole_0(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_40,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
             => ( v2_funct_1(X3)
                & v2_funct_2(X4,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_funct_2])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_28])])).

fof(c_0_46,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    & r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))
    & ( ~ v2_funct_1(esk5_0)
      | ~ v2_funct_2(esk6_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

fof(c_0_48,plain,(
    ! [X31] :
      ( k1_relat_1(k6_relat_1(X31)) = X31
      & k2_relat_1(k6_relat_1(X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_49,plain,
    ( r1_tarski(k6_relat_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_45])).

fof(c_0_50,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ r2_relset_1(X36,X37,X38,X39)
        | X38 = X39
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X38 != X39
        | r2_relset_1(X36,X37,X38,X39)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_51,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_47])).

cnf(c_0_53,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_49])).

fof(c_0_55,plain,(
    ! [X32] :
      ( v1_relat_1(k6_relat_1(X32))
      & v2_funct_1(k6_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_56,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_36])).

cnf(c_0_58,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_52])).

cnf(c_0_59,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_61,plain,(
    ! [X33,X34,X35] :
      ( ( v4_relat_1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v5_relat_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_62,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_relat_1(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_63,plain,(
    ! [X27,X28] : v1_relat_1(k2_zfmisc_1(X27,X28)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_64,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_relat_1(X30)
      | r1_tarski(k2_relat_1(k5_relat_1(X29,X30)),k2_relat_1(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_65,plain,(
    ! [X49,X50,X51,X52,X53,X54] :
      ( ~ v1_funct_1(X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ v1_funct_1(X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_partfun1(X49,X50,X51,X52,X53,X54) = k5_relat_1(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_66,plain,(
    ! [X56,X57,X58,X59,X60] :
      ( ( X58 = k1_xboole_0
        | v2_funct_1(X59)
        | ~ v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X57,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( X57 != k1_xboole_0
        | v2_funct_1(X59)
        | ~ v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X57,X58)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X56,X57)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_67,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( k6_relat_1(esk3_0) = k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40])])).

cnf(c_0_69,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(k2_zfmisc_1(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_58]),c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_60])).

fof(c_0_71,plain,(
    ! [X25,X26] :
      ( ( ~ v5_relat_1(X26,X25)
        | r1_tarski(k2_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k2_relat_1(X26),X25)
        | v5_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_72,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_74,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( v2_funct_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0))
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_84,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ( v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_85,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_29])).

cnf(c_0_86,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_29])).

cnf(c_0_87,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( v5_relat_1(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_73]),c_0_75])])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6)),k2_relat_1(X6))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)) = esk3_0
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_68])).

cnf(c_0_92,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_60]),c_0_75])])).

cnf(c_0_93,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v2_funct_1(esk5_0)
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_81]),c_0_82]),c_0_83]),c_0_73]),c_0_60])])).

cnf(c_0_94,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_95,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_54])).

cnf(c_0_96,negated_conjecture,
    ( k1_xboole_0 = esk5_0
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

fof(c_0_97,plain,(
    ! [X40,X41] :
      ( ( ~ v2_funct_2(X41,X40)
        | k2_relat_1(X41) = X40
        | ~ v1_relat_1(X41)
        | ~ v5_relat_1(X41,X40) )
      & ( k2_relat_1(X41) != X40
        | v2_funct_2(X41,X40)
        | ~ v1_relat_1(X41)
        | ~ v5_relat_1(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_98,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(esk3_0,k2_relat_1(esk6_0))
    | ~ m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_82]),c_0_83]),c_0_89]),c_0_92]),c_0_73]),c_0_60])])).

cnf(c_0_100,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_82]),c_0_83]),c_0_73]),c_0_60])])).

cnf(c_0_101,negated_conjecture,
    ( v2_funct_1(esk5_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_102,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk3_0
    | ~ r1_tarski(esk3_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(esk3_0,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_94]),c_0_82]),c_0_83]),c_0_73]),c_0_60])])).

cnf(c_0_105,negated_conjecture,
    ( ~ v2_funct_1(esk5_0)
    | ~ v2_funct_2(esk6_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_106,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_100]),c_0_101])).

cnf(c_0_107,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_109,negated_conjecture,
    ( ~ v2_funct_2(esk6_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106])])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_88]),c_0_89])]),c_0_109]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.43  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.43  #
% 0.21/0.43  # Preprocessing time       : 0.029 s
% 0.21/0.43  # Presaturation interreduction done
% 0.21/0.43  
% 0.21/0.43  # Proof found!
% 0.21/0.43  # SZS status Theorem
% 0.21/0.43  # SZS output start CNFRefutation
% 0.21/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.43  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.21/0.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.43  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.43  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.21/0.43  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.21/0.43  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.21/0.43  fof(t29_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 0.21/0.43  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.21/0.43  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.21/0.43  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.21/0.43  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.43  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.43  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.43  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 0.21/0.43  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.21/0.43  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 0.21/0.43  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.21/0.43  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.21/0.43  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.21/0.43  fof(c_0_21, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.43  fof(c_0_22, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.43  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.43  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.43  fof(c_0_25, plain, ![X19, X20]:(~v1_xboole_0(X19)|v1_xboole_0(k2_zfmisc_1(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.21/0.43  fof(c_0_26, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.43  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.43  cnf(c_0_28, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.43  cnf(c_0_29, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.43  fof(c_0_30, plain, ![X48]:(v1_partfun1(k6_partfun1(X48),X48)&m1_subset_1(k6_partfun1(X48),k1_zfmisc_1(k2_zfmisc_1(X48,X48)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.21/0.43  fof(c_0_31, plain, ![X55]:k6_partfun1(X55)=k6_relat_1(X55), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.21/0.43  cnf(c_0_32, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.43  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.43  cnf(c_0_34, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_29])).
% 0.21/0.43  cnf(c_0_35, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.43  cnf(c_0_36, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.43  cnf(c_0_37, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.43  cnf(c_0_38, plain, (r1_tarski(k2_zfmisc_1(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_34, c_0_28])).
% 0.21/0.43  fof(c_0_39, plain, ![X21, X22]:(~v1_xboole_0(X21)|(~m1_subset_1(X22,k1_zfmisc_1(X21))|v1_xboole_0(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.21/0.43  cnf(c_0_40, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.43  cnf(c_0_41, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.21/0.43  cnf(c_0_42, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.43  cnf(c_0_43, plain, (m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.43  fof(c_0_44, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1)))))), inference(assume_negation,[status(cth)],[t29_funct_2])).
% 0.21/0.43  cnf(c_0_45, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_28])])).
% 0.21/0.43  fof(c_0_46, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))&(~v2_funct_1(esk5_0)|~v2_funct_2(esk6_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 0.21/0.43  cnf(c_0_47, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.21/0.43  fof(c_0_48, plain, ![X31]:(k1_relat_1(k6_relat_1(X31))=X31&k2_relat_1(k6_relat_1(X31))=X31), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.21/0.43  cnf(c_0_49, plain, (r1_tarski(k6_relat_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_45])).
% 0.21/0.43  fof(c_0_50, plain, ![X36, X37, X38, X39]:((~r2_relset_1(X36,X37,X38,X39)|X38=X39|(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(X38!=X39|r2_relset_1(X36,X37,X38,X39)|(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.21/0.43  cnf(c_0_51, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_partfun1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  cnf(c_0_52, plain, (r1_tarski(k6_relat_1(X1),X2)|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_27, c_0_47])).
% 0.21/0.43  cnf(c_0_53, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.43  cnf(c_0_54, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_49])).
% 0.21/0.43  fof(c_0_55, plain, ![X32]:(v1_relat_1(k6_relat_1(X32))&v2_funct_1(k6_relat_1(X32))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.21/0.43  cnf(c_0_56, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.43  cnf(c_0_57, negated_conjecture, (r2_relset_1(esk3_0,esk3_0,k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k6_relat_1(esk3_0))), inference(rw,[status(thm)],[c_0_51, c_0_36])).
% 0.21/0.43  cnf(c_0_58, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(spm,[status(thm)],[c_0_37, c_0_52])).
% 0.21/0.43  cnf(c_0_59, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.43  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  fof(c_0_61, plain, ![X33, X34, X35]:((v4_relat_1(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v5_relat_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.43  fof(c_0_62, plain, ![X23, X24]:(~v1_relat_1(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_relat_1(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.43  fof(c_0_63, plain, ![X27, X28]:v1_relat_1(k2_zfmisc_1(X27,X28)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.43  fof(c_0_64, plain, ![X29, X30]:(~v1_relat_1(X29)|(~v1_relat_1(X30)|r1_tarski(k2_relat_1(k5_relat_1(X29,X30)),k2_relat_1(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.21/0.43  fof(c_0_65, plain, ![X49, X50, X51, X52, X53, X54]:(~v1_funct_1(X53)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k1_partfun1(X49,X50,X51,X52,X53,X54)=k5_relat_1(X53,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.21/0.43  fof(c_0_66, plain, ![X56, X57, X58, X59, X60]:((X58=k1_xboole_0|v2_funct_1(X59)|~v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))|(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(X57!=k1_xboole_0|v2_funct_1(X59)|~v2_funct_1(k1_partfun1(X56,X57,X57,X58,X59,X60))|(~v1_funct_1(X60)|~v1_funct_2(X60,X57,X58)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X57,X58))))|(~v1_funct_1(X59)|~v1_funct_2(X59,X56,X57)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.21/0.43  cnf(c_0_67, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.43  cnf(c_0_68, negated_conjecture, (k6_relat_1(esk3_0)=k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0)|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_40])])).
% 0.21/0.43  cnf(c_0_69, plain, (k1_xboole_0=X1|~v1_xboole_0(k2_zfmisc_1(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_58]), c_0_59])).
% 0.21/0.43  cnf(c_0_70, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_42, c_0_60])).
% 0.21/0.43  fof(c_0_71, plain, ![X25, X26]:((~v5_relat_1(X26,X25)|r1_tarski(k2_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k2_relat_1(X26),X25)|v5_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.21/0.43  cnf(c_0_72, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.43  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  cnf(c_0_74, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.43  cnf(c_0_75, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.43  cnf(c_0_76, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.43  cnf(c_0_77, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.21/0.43  cnf(c_0_78, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.21/0.43  cnf(c_0_79, negated_conjecture, (v2_funct_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0))|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.21/0.43  cnf(c_0_80, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  cnf(c_0_81, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  cnf(c_0_82, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  cnf(c_0_83, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  fof(c_0_84, plain, ![X42, X43, X44, X45, X46, X47]:((v1_funct_1(k1_partfun1(X42,X43,X44,X45,X46,X47))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(m1_subset_1(k1_partfun1(X42,X43,X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(X42,X45)))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.21/0.43  cnf(c_0_85, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_69, c_0_29])).
% 0.21/0.43  cnf(c_0_86, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_70, c_0_29])).
% 0.21/0.43  cnf(c_0_87, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.21/0.43  cnf(c_0_88, negated_conjecture, (v5_relat_1(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.21/0.43  cnf(c_0_89, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_73]), c_0_75])])).
% 0.21/0.43  cnf(c_0_90, plain, (r1_tarski(k2_relat_1(k1_partfun1(X1,X2,X3,X4,X5,X6)),k2_relat_1(X6))|~v1_funct_1(X6)|~v1_funct_1(X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.43  cnf(c_0_91, negated_conjecture, (k2_relat_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0))=esk3_0|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_53, c_0_68])).
% 0.21/0.43  cnf(c_0_92, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_60]), c_0_75])])).
% 0.21/0.43  cnf(c_0_93, negated_conjecture, (k1_xboole_0=esk3_0|v2_funct_1(esk5_0)|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_81]), c_0_82]), c_0_83]), c_0_73]), c_0_60])])).
% 0.21/0.43  cnf(c_0_94, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.21/0.43  cnf(c_0_95, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_54])).
% 0.21/0.43  cnf(c_0_96, negated_conjecture, (k1_xboole_0=esk5_0|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.21/0.43  fof(c_0_97, plain, ![X40, X41]:((~v2_funct_2(X41,X40)|k2_relat_1(X41)=X40|(~v1_relat_1(X41)|~v5_relat_1(X41,X40)))&(k2_relat_1(X41)!=X40|v2_funct_2(X41,X40)|(~v1_relat_1(X41)|~v5_relat_1(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.21/0.43  cnf(c_0_98, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])])).
% 0.21/0.43  cnf(c_0_99, negated_conjecture, (r1_tarski(esk3_0,k2_relat_1(esk6_0))|~m1_subset_1(k1_partfun1(esk3_0,esk4_0,esk4_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_82]), c_0_83]), c_0_89]), c_0_92]), c_0_73]), c_0_60])])).
% 0.21/0.43  cnf(c_0_100, negated_conjecture, (k1_xboole_0=esk3_0|v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_82]), c_0_83]), c_0_73]), c_0_60])])).
% 0.21/0.43  cnf(c_0_101, negated_conjecture, (v2_funct_1(esk5_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.21/0.43  cnf(c_0_102, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.21/0.43  cnf(c_0_103, negated_conjecture, (k2_relat_1(esk6_0)=esk3_0|~r1_tarski(esk3_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_98])).
% 0.21/0.43  cnf(c_0_104, negated_conjecture, (r1_tarski(esk3_0,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_94]), c_0_82]), c_0_83]), c_0_73]), c_0_60])])).
% 0.21/0.43  cnf(c_0_105, negated_conjecture, (~v2_funct_1(esk5_0)|~v2_funct_2(esk6_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.43  cnf(c_0_106, negated_conjecture, (v2_funct_1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_100]), c_0_101])).
% 0.21/0.43  cnf(c_0_107, plain, (v2_funct_2(X1,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_102])).
% 0.21/0.43  cnf(c_0_108, negated_conjecture, (k2_relat_1(esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 0.21/0.43  cnf(c_0_109, negated_conjecture, (~v2_funct_2(esk6_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106])])).
% 0.21/0.43  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_88]), c_0_89])]), c_0_109]), ['proof']).
% 0.21/0.43  # SZS output end CNFRefutation
% 0.21/0.43  # Proof object total steps             : 111
% 0.21/0.43  # Proof object clause steps            : 69
% 0.21/0.43  # Proof object formula steps           : 42
% 0.21/0.43  # Proof object conjectures             : 32
% 0.21/0.43  # Proof object clause conjectures      : 29
% 0.21/0.43  # Proof object formula conjectures     : 3
% 0.21/0.43  # Proof object initial clauses used    : 28
% 0.21/0.43  # Proof object initial formulas used   : 21
% 0.21/0.43  # Proof object generating inferences   : 36
% 0.21/0.43  # Proof object simplifying inferences  : 47
% 0.21/0.43  # Training examples: 0 positive, 0 negative
% 0.21/0.43  # Parsed axioms                        : 21
% 0.21/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.43  # Initial clauses                      : 42
% 0.21/0.43  # Removed in clause preprocessing      : 1
% 0.21/0.43  # Initial clauses in saturation        : 41
% 0.21/0.43  # Processed clauses                    : 731
% 0.21/0.43  # ...of these trivial                  : 1
% 0.21/0.43  # ...subsumed                          : 347
% 0.21/0.43  # ...remaining for further processing  : 383
% 0.21/0.43  # Other redundant clauses eliminated   : 5
% 0.21/0.43  # Clauses deleted for lack of memory   : 0
% 0.21/0.43  # Backward-subsumed                    : 23
% 0.21/0.43  # Backward-rewritten                   : 18
% 0.21/0.43  # Generated clauses                    : 1917
% 0.21/0.43  # ...of the previous two non-trivial   : 1717
% 0.21/0.43  # Contextual simplify-reflections      : 9
% 0.21/0.43  # Paramodulations                      : 1912
% 0.21/0.43  # Factorizations                       : 0
% 0.21/0.43  # Equation resolutions                 : 5
% 0.21/0.43  # Propositional unsat checks           : 0
% 0.21/0.43  #    Propositional check models        : 0
% 0.21/0.43  #    Propositional check unsatisfiable : 0
% 0.21/0.43  #    Propositional clauses             : 0
% 0.21/0.43  #    Propositional clauses after purity: 0
% 0.21/0.43  #    Propositional unsat core size     : 0
% 0.21/0.43  #    Propositional preprocessing time  : 0.000
% 0.21/0.43  #    Propositional encoding time       : 0.000
% 0.21/0.43  #    Propositional solver time         : 0.000
% 0.21/0.43  #    Success case prop preproc time    : 0.000
% 0.21/0.43  #    Success case prop encoding time   : 0.000
% 0.21/0.43  #    Success case prop solver time     : 0.000
% 0.21/0.43  # Current number of processed clauses  : 297
% 0.21/0.43  #    Positive orientable unit clauses  : 40
% 0.21/0.43  #    Positive unorientable unit clauses: 0
% 0.21/0.43  #    Negative unit clauses             : 1
% 0.21/0.43  #    Non-unit-clauses                  : 256
% 0.21/0.43  # Current number of unprocessed clauses: 1030
% 0.21/0.43  # ...number of literals in the above   : 4208
% 0.21/0.43  # Current number of archived formulas  : 0
% 0.21/0.43  # Current number of archived clauses   : 82
% 0.21/0.43  # Clause-clause subsumption calls (NU) : 20962
% 0.21/0.43  # Rec. Clause-clause subsumption calls : 14241
% 0.21/0.43  # Non-unit clause-clause subsumptions  : 374
% 0.21/0.43  # Unit Clause-clause subsumption calls : 293
% 0.21/0.43  # Rewrite failures with RHS unbound    : 0
% 0.21/0.43  # BW rewrite match attempts            : 6
% 0.21/0.43  # BW rewrite match successes           : 6
% 0.21/0.43  # Condensation attempts                : 0
% 0.21/0.43  # Condensation successes               : 0
% 0.21/0.43  # Termbank termtop insertions          : 27611
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.079 s
% 0.21/0.43  # System time              : 0.006 s
% 0.21/0.43  # Total time               : 0.086 s
% 0.21/0.43  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
