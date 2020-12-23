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
% DateTime   : Thu Dec  3 11:02:39 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  157 (1587 expanded)
%              Number of clauses        :  102 ( 648 expanded)
%              Number of leaves         :   28 ( 417 expanded)
%              Depth                    :   17
%              Number of atoms          :  481 (6678 expanded)
%              Number of equality atoms :  101 ( 989 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t31_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t14_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
     => ( r1_tarski(k2_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t9_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t63_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(t53_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(c_0_28,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_31,plain,(
    ! [X17,X18,X19] :
      ( ~ r2_hidden(X17,X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X19))
      | ~ v1_xboole_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_36,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_40,plain,(
    ! [X43,X44,X45] :
      ( ( v4_relat_1(X45,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( v5_relat_1(X45,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_41,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

fof(c_0_42,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | v1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_43,plain,(
    ! [X58] :
      ( ( v1_funct_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( v1_funct_2(X58,k1_relat_1(X58),k2_relat_1(X58))
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X58),k2_relat_1(X58))))
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_46,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
      | ~ r1_tarski(k2_relat_1(X52),X50)
      | m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X50))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).

fof(c_0_47,plain,(
    ! [X37] :
      ( ( k2_relat_1(X37) = k1_relat_1(k2_funct_1(X37))
        | ~ v2_funct_1(X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( k1_relat_1(X37) = k2_relat_1(k2_funct_1(X37))
        | ~ v2_funct_1(X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_48,plain,(
    ! [X20,X21] :
      ( ( ~ v4_relat_1(X21,X20)
        | r1_tarski(k1_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(k1_relat_1(X21),X20)
        | v4_relat_1(X21,X20)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_49,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

fof(c_0_59,plain,(
    ! [X28] :
      ( ( v1_relat_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_60,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | k2_relset_1(X46,X47,X48) = k2_relat_1(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_61,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_52])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_45])).

fof(c_0_63,plain,(
    ! [X26] :
      ( k1_relat_1(k6_relat_1(X26)) = X26
      & k2_relat_1(k6_relat_1(X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_64,plain,(
    ! [X29] :
      ( v1_relat_1(k6_relat_1(X29))
      & v1_funct_1(k6_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_65,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_66,plain,(
    ! [X56] :
      ( v1_partfun1(k6_partfun1(X56),X56)
      & m1_subset_1(k6_partfun1(X56),k1_zfmisc_1(k2_zfmisc_1(X56,X56))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_67,plain,(
    ! [X57] : k6_partfun1(X57) = k6_relat_1(X57) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_68,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k1_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_70,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_72,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_73,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_74,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_75,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_77,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_78,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_79,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_81,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_83,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_84,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71]),c_0_58])])).

cnf(c_0_87,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_50]),c_0_76])).

cnf(c_0_89,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80]),c_0_81])])).

cnf(c_0_90,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_91,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_92,plain,(
    ! [X59,X60,X61,X62] :
      ( ( v1_funct_1(X62)
        | X60 = k1_xboole_0
        | ~ r1_tarski(X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v1_funct_2(X62,X59,X61)
        | X60 = k1_xboole_0
        | ~ r1_tarski(X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X61)))
        | X60 = k1_xboole_0
        | ~ r1_tarski(X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v1_funct_1(X62)
        | X59 != k1_xboole_0
        | ~ r1_tarski(X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( v1_funct_2(X62,X59,X61)
        | X59 != k1_xboole_0
        | ~ r1_tarski(X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) )
      & ( m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X61)))
        | X59 != k1_xboole_0
        | ~ r1_tarski(X60,X61)
        | ~ v1_funct_1(X62)
        | ~ v1_funct_2(X62,X59,X60)
        | ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).

cnf(c_0_93,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_94,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_96,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k10_relat_1(X23,k2_relat_1(X23)) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_97,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X38)
      | ~ v1_funct_1(X38)
      | ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v2_funct_1(X38)
      | k2_relat_1(X38) != k1_relat_1(X39)
      | k5_relat_1(X38,X39) != k6_relat_1(k1_relat_1(X38))
      | X39 = k2_funct_1(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).

fof(c_0_98,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | k5_relat_1(X35,X36) != k6_relat_1(k1_relat_1(X35))
      | v2_funct_1(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).

fof(c_0_99,plain,(
    ! [X27] :
      ( ~ v1_relat_1(X27)
      | k5_relat_1(X27,k6_relat_1(k2_relat_1(X27))) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_100,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_101,plain,(
    ! [X53,X54,X55] :
      ( ( v1_funct_1(X55)
        | ~ v1_funct_1(X55)
        | ~ v1_partfun1(X55,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( v1_funct_2(X55,X53,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_partfun1(X55,X53)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_74]),c_0_71])]),c_0_58])])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_70]),c_0_71]),c_0_58])])).

cnf(c_0_104,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])])).

cnf(c_0_105,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_106,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_55]),c_0_73]),c_0_74])).

cnf(c_0_107,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_55]),c_0_73]),c_0_74])).

fof(c_0_108,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ r1_tarski(X31,k2_relat_1(X32))
      | k9_relat_1(X32,k10_relat_1(X32,X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_109,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(X1,X1))
    | ~ r2_hidden(X2,k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_94])).

cnf(c_0_110,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_111,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_112,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_113,plain,
    ( v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_114,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_115,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_100])).

cnf(c_0_116,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_100])).

fof(c_0_117,plain,(
    ! [X30] :
      ( v1_relat_1(k6_relat_1(X30))
      & v2_funct_1(k6_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_118,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_120,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_121,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_39])).

cnf(c_0_122,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_88]),c_0_71]),c_0_58])])).

cnf(c_0_124,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_74]),c_0_107])).

cnf(c_0_125,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_126,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_91]),c_0_100])])).

cnf(c_0_127,plain,
    ( k10_relat_1(k2_funct_1(X1),k1_relat_1(X1)) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_55]),c_0_73])).

cnf(c_0_128,plain,
    ( X1 = k2_funct_1(X2)
    | k5_relat_1(X2,X1) != k6_relat_1(k1_relat_1(X2))
    | k2_relat_1(X2) != k1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_129,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_100]),c_0_116])])).

cnf(c_0_130,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_100])).

cnf(c_0_131,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_100])).

cnf(c_0_132,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_133,negated_conjecture,
    ( ~ v1_partfun1(k2_funct_1(esk4_0),esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_103]),c_0_119])).

cnf(c_0_134,plain,
    ( v1_partfun1(k6_relat_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_120,c_0_84])).

cnf(c_0_135,plain,
    ( k6_relat_1(X1) = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_121])).

cnf(c_0_136,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_137,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk4_0),k1_relat_1(k2_funct_1(esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_69]),c_0_70]),c_0_71]),c_0_58])])).

cnf(c_0_138,negated_conjecture,
    ( k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1)) = X1
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_88]),c_0_71]),c_0_58])])).

cnf(c_0_139,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_39])).

cnf(c_0_140,plain,
    ( k10_relat_1(X1,k1_relat_1(X2)) = k1_relat_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(k2_funct_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_62])).

cnf(c_0_141,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130]),c_0_100]),c_0_115]),c_0_130]),c_0_131]),c_0_116])])).

cnf(c_0_142,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_100])).

cnf(c_0_143,negated_conjecture,
    ( k10_relat_1(esk4_0,esk3_0) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_88]),c_0_58])])).

cnf(c_0_144,negated_conjecture,
    ( ~ v1_partfun1(k2_funct_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_74]),c_0_71]),c_0_58])])).

cnf(c_0_145,plain,
    ( v1_partfun1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_146,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0) = esk4_0
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_136])).

cnf(c_0_147,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_72]),c_0_88]),c_0_70]),c_0_71]),c_0_58])]),c_0_119])).

cnf(c_0_148,negated_conjecture,
    ( k9_relat_1(esk4_0,k10_relat_1(esk4_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_149,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_130]),c_0_142]),c_0_131]),c_0_116]),c_0_91])])).

cnf(c_0_150,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_relat_1(esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_33]),c_0_143])).

cnf(c_0_151,negated_conjecture,
    ( ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_152,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_146,c_0_147]),c_0_110]),c_0_147]),c_0_110]),c_0_91])])).

cnf(c_0_153,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_152]),c_0_141]),c_0_91])])).

cnf(c_0_155,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_153,c_0_152]),c_0_91])])).

cnf(c_0_156,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_155]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.66  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.46/0.66  # and selection function SelectNewComplexAHPNS.
% 0.46/0.66  #
% 0.46/0.66  # Preprocessing time       : 0.018 s
% 0.46/0.66  # Presaturation interreduction done
% 0.46/0.66  
% 0.46/0.66  # Proof found!
% 0.46/0.66  # SZS status Theorem
% 0.46/0.66  # SZS output start CNFRefutation
% 0.46/0.66  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.46/0.66  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.46/0.66  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.46/0.66  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.46/0.66  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.46/0.66  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.46/0.66  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.46/0.66  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.46/0.66  fof(t14_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))=>(r1_tarski(k2_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 0.46/0.66  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.46/0.66  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.46/0.66  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.46/0.66  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.46/0.66  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.46/0.66  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.46/0.66  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.46/0.66  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.46/0.66  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.46/0.66  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.46/0.66  fof(t9_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.46/0.66  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.46/0.66  fof(t63_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 0.46/0.66  fof(t53_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 0.46/0.66  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.46/0.66  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.46/0.66  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.46/0.66  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.46/0.66  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.46/0.66  fof(c_0_28, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.46/0.66  fof(c_0_29, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.46/0.66  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  fof(c_0_31, plain, ![X17, X18, X19]:(~r2_hidden(X17,X18)|~m1_subset_1(X18,k1_zfmisc_1(X19))|~v1_xboole_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.46/0.66  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.46/0.66  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 0.46/0.66  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.66  cnf(c_0_35, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.46/0.66  fof(c_0_36, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.46/0.66  fof(c_0_37, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.46/0.66  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.46/0.66  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.46/0.66  fof(c_0_40, plain, ![X43, X44, X45]:((v4_relat_1(X45,X43)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))&(v5_relat_1(X45,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.46/0.66  fof(c_0_41, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v2_funct_1(esk4_0)&k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.46/0.66  fof(c_0_42, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.46/0.66  fof(c_0_43, plain, ![X58]:(((v1_funct_1(X58)|(~v1_relat_1(X58)|~v1_funct_1(X58)))&(v1_funct_2(X58,k1_relat_1(X58),k2_relat_1(X58))|(~v1_relat_1(X58)|~v1_funct_1(X58))))&(m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X58),k2_relat_1(X58))))|(~v1_relat_1(X58)|~v1_funct_1(X58)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.46/0.66  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.46/0.66  fof(c_0_46, plain, ![X49, X50, X51, X52]:(~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))|(~r1_tarski(k2_relat_1(X52),X50)|m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X51,X50))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_relset_1])])).
% 0.46/0.66  fof(c_0_47, plain, ![X37]:((k2_relat_1(X37)=k1_relat_1(k2_funct_1(X37))|~v2_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(k1_relat_1(X37)=k2_relat_1(k2_funct_1(X37))|~v2_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.46/0.66  fof(c_0_48, plain, ![X20, X21]:((~v4_relat_1(X21,X20)|r1_tarski(k1_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_tarski(k1_relat_1(X21),X20)|v4_relat_1(X21,X20)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.46/0.66  cnf(c_0_49, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.46/0.66  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.46/0.66  cnf(c_0_51, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.46/0.66  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.46/0.66  cnf(c_0_53, plain, (X1=X2|~v1_xboole_0(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.46/0.66  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.46/0.66  cnf(c_0_55, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.46/0.66  cnf(c_0_56, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.46/0.66  cnf(c_0_57, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.46/0.66  cnf(c_0_58, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 0.46/0.66  fof(c_0_59, plain, ![X28]:((v1_relat_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.46/0.66  fof(c_0_60, plain, ![X46, X47, X48]:(~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|k2_relset_1(X46,X47,X48)=k2_relat_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.46/0.66  cnf(c_0_61, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_52])).
% 0.46/0.66  cnf(c_0_62, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_53, c_0_45])).
% 0.46/0.66  fof(c_0_63, plain, ![X26]:(k1_relat_1(k6_relat_1(X26))=X26&k2_relat_1(k6_relat_1(X26))=X26), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.46/0.66  fof(c_0_64, plain, ![X29]:(v1_relat_1(k6_relat_1(X29))&v1_funct_1(k6_relat_1(X29))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.46/0.66  fof(c_0_65, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.46/0.66  fof(c_0_66, plain, ![X56]:(v1_partfun1(k6_partfun1(X56),X56)&m1_subset_1(k6_partfun1(X56),k1_zfmisc_1(k2_zfmisc_1(X56,X56)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.46/0.66  fof(c_0_67, plain, ![X57]:k6_partfun1(X57)=k6_relat_1(X57), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.46/0.66  cnf(c_0_68, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~r1_tarski(k1_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.46/0.66  cnf(c_0_69, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.46/0.66  cnf(c_0_70, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.46/0.66  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.46/0.66  cnf(c_0_72, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.46/0.66  cnf(c_0_73, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.66  cnf(c_0_74, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.66  cnf(c_0_75, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.46/0.66  cnf(c_0_76, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.46/0.66  cnf(c_0_77, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_xboole_0(k2_relat_1(X1))|~v1_xboole_0(X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.46/0.66  cnf(c_0_78, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.46/0.66  cnf(c_0_79, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.46/0.66  cnf(c_0_80, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.46/0.66  cnf(c_0_81, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.46/0.66  cnf(c_0_82, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.46/0.66  cnf(c_0_83, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.46/0.66  cnf(c_0_84, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.46/0.66  cnf(c_0_85, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.46/0.66  cnf(c_0_86, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71]), c_0_58])])).
% 0.46/0.66  cnf(c_0_87, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_72]), c_0_73]), c_0_74])).
% 0.46/0.66  cnf(c_0_88, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_50]), c_0_76])).
% 0.46/0.66  cnf(c_0_89, plain, (~v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)|~v1_xboole_0(X2)|~r2_hidden(X3,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_80]), c_0_81])])).
% 0.46/0.66  cnf(c_0_90, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_82])).
% 0.46/0.66  cnf(c_0_91, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.46/0.66  fof(c_0_92, plain, ![X59, X60, X61, X62]:((((v1_funct_1(X62)|X60=k1_xboole_0|~r1_tarski(X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(v1_funct_2(X62,X59,X61)|X60=k1_xboole_0|~r1_tarski(X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))))&(m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X61)))|X60=k1_xboole_0|~r1_tarski(X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))))&(((v1_funct_1(X62)|X59!=k1_xboole_0|~r1_tarski(X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))))&(v1_funct_2(X62,X59,X61)|X59!=k1_xboole_0|~r1_tarski(X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))))&(m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X61)))|X59!=k1_xboole_0|~r1_tarski(X60,X61)|(~v1_funct_1(X62)|~v1_funct_2(X62,X59,X60)|~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X59,X60))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).
% 0.46/0.66  cnf(c_0_93, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.46/0.66  cnf(c_0_94, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 0.46/0.66  cnf(c_0_95, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.46/0.66  fof(c_0_96, plain, ![X23]:(~v1_relat_1(X23)|k10_relat_1(X23,k2_relat_1(X23))=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.46/0.66  fof(c_0_97, plain, ![X38, X39]:(~v1_relat_1(X38)|~v1_funct_1(X38)|(~v1_relat_1(X39)|~v1_funct_1(X39)|(~v2_funct_1(X38)|k2_relat_1(X38)!=k1_relat_1(X39)|k5_relat_1(X38,X39)!=k6_relat_1(k1_relat_1(X38))|X39=k2_funct_1(X38)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).
% 0.46/0.66  fof(c_0_98, plain, ![X35, X36]:(~v1_relat_1(X35)|~v1_funct_1(X35)|(~v1_relat_1(X36)|~v1_funct_1(X36)|k5_relat_1(X35,X36)!=k6_relat_1(k1_relat_1(X35))|v2_funct_1(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).
% 0.46/0.66  fof(c_0_99, plain, ![X27]:(~v1_relat_1(X27)|k5_relat_1(X27,k6_relat_1(k2_relat_1(X27)))=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.46/0.66  cnf(c_0_100, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.46/0.66  fof(c_0_101, plain, ![X53, X54, X55]:((v1_funct_1(X55)|(~v1_funct_1(X55)|~v1_partfun1(X55,X53))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))&(v1_funct_2(X55,X53,X54)|(~v1_funct_1(X55)|~v1_partfun1(X55,X53))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.46/0.66  cnf(c_0_102, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_74]), c_0_71])]), c_0_58])])).
% 0.46/0.66  cnf(c_0_103, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88]), c_0_70]), c_0_71]), c_0_58])])).
% 0.46/0.66  cnf(c_0_104, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])])).
% 0.46/0.66  cnf(c_0_105, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.46/0.66  cnf(c_0_106, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_55]), c_0_73]), c_0_74])).
% 0.46/0.66  cnf(c_0_107, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_55]), c_0_73]), c_0_74])).
% 0.46/0.66  fof(c_0_108, plain, ![X31, X32]:(~v1_relat_1(X32)|~v1_funct_1(X32)|(~r1_tarski(X31,k2_relat_1(X32))|k9_relat_1(X32,k10_relat_1(X32,X31))=X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.46/0.66  cnf(c_0_109, plain, (~v1_xboole_0(k2_zfmisc_1(X1,X1))|~r2_hidden(X2,k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_34, c_0_94])).
% 0.46/0.66  cnf(c_0_110, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_95])).
% 0.46/0.66  cnf(c_0_111, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.46/0.66  cnf(c_0_112, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.46/0.66  cnf(c_0_113, plain, (v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.46/0.66  cnf(c_0_114, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.46/0.66  cnf(c_0_115, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_100])).
% 0.46/0.66  cnf(c_0_116, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_80, c_0_100])).
% 0.46/0.66  fof(c_0_117, plain, ![X30]:(v1_relat_1(k6_relat_1(X30))&v2_funct_1(k6_relat_1(X30))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.46/0.66  cnf(c_0_118, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.46/0.66  cnf(c_0_119, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103])])).
% 0.46/0.66  cnf(c_0_120, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.46/0.66  cnf(c_0_121, plain, (r1_tarski(k6_relat_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_104, c_0_39])).
% 0.46/0.66  cnf(c_0_122, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.46/0.66  cnf(c_0_123, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_88]), c_0_71]), c_0_58])])).
% 0.46/0.66  cnf(c_0_124, plain, (k1_relat_1(X1)=k1_xboole_0|v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_74]), c_0_107])).
% 0.46/0.66  cnf(c_0_125, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.46/0.66  cnf(c_0_126, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_91]), c_0_100])])).
% 0.46/0.66  cnf(c_0_127, plain, (k10_relat_1(k2_funct_1(X1),k1_relat_1(X1))=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_55]), c_0_73])).
% 0.46/0.66  cnf(c_0_128, plain, (X1=k2_funct_1(X2)|k5_relat_1(X2,X1)!=k6_relat_1(k1_relat_1(X2))|k2_relat_1(X2)!=k1_relat_1(X1)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[c_0_112, c_0_113])).
% 0.46/0.66  cnf(c_0_129, plain, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_100]), c_0_116])])).
% 0.46/0.66  cnf(c_0_130, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_100])).
% 0.46/0.66  cnf(c_0_131, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_79, c_0_100])).
% 0.46/0.66  cnf(c_0_132, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.46/0.66  cnf(c_0_133, negated_conjecture, (~v1_partfun1(k2_funct_1(esk4_0),esk3_0)|~v1_funct_1(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_103]), c_0_119])).
% 0.46/0.66  cnf(c_0_134, plain, (v1_partfun1(k6_relat_1(X1),X1)), inference(rw,[status(thm)],[c_0_120, c_0_84])).
% 0.46/0.66  cnf(c_0_135, plain, (k6_relat_1(X1)=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_53, c_0_121])).
% 0.46/0.66  cnf(c_0_136, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.46/0.66  cnf(c_0_137, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk4_0),k1_relat_1(k2_funct_1(esk4_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_69]), c_0_70]), c_0_71]), c_0_58])])).
% 0.46/0.66  cnf(c_0_138, negated_conjecture, (k9_relat_1(esk4_0,k10_relat_1(esk4_0,X1))=X1|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_88]), c_0_71]), c_0_58])])).
% 0.46/0.66  cnf(c_0_139, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_126, c_0_39])).
% 0.46/0.66  cnf(c_0_140, plain, (k10_relat_1(X1,k1_relat_1(X2))=k1_relat_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_xboole_0(k2_funct_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_127, c_0_62])).
% 0.46/0.66  cnf(c_0_141, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130]), c_0_100]), c_0_115]), c_0_130]), c_0_131]), c_0_116])])).
% 0.46/0.66  cnf(c_0_142, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_132, c_0_100])).
% 0.46/0.66  cnf(c_0_143, negated_conjecture, (k10_relat_1(esk4_0,esk3_0)=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_88]), c_0_58])])).
% 0.46/0.66  cnf(c_0_144, negated_conjecture, (~v1_partfun1(k2_funct_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_74]), c_0_71]), c_0_58])])).
% 0.46/0.66  cnf(c_0_145, plain, (v1_partfun1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 0.46/0.66  cnf(c_0_146, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)=esk4_0|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))), inference(spm,[status(thm)],[c_0_53, c_0_136])).
% 0.46/0.66  cnf(c_0_147, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_72]), c_0_88]), c_0_70]), c_0_71]), c_0_58])]), c_0_119])).
% 0.46/0.66  cnf(c_0_148, negated_conjecture, (k9_relat_1(esk4_0,k10_relat_1(esk4_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 0.46/0.66  cnf(c_0_149, plain, (k10_relat_1(X1,k1_xboole_0)=k1_relat_1(X1)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_130]), c_0_142]), c_0_131]), c_0_116]), c_0_91])])).
% 0.46/0.66  cnf(c_0_150, negated_conjecture, (k9_relat_1(esk4_0,k1_relat_1(esk4_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_33]), c_0_143])).
% 0.46/0.66  cnf(c_0_151, negated_conjecture, (~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.46/0.66  cnf(c_0_152, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_146, c_0_147]), c_0_110]), c_0_147]), c_0_110]), c_0_91])])).
% 0.46/0.66  cnf(c_0_153, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_150])).
% 0.46/0.66  cnf(c_0_154, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_152]), c_0_141]), c_0_91])])).
% 0.46/0.66  cnf(c_0_155, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_153, c_0_152]), c_0_91])])).
% 0.46/0.66  cnf(c_0_156, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_154, c_0_155]), c_0_91])]), ['proof']).
% 0.46/0.66  # SZS output end CNFRefutation
% 0.46/0.66  # Proof object total steps             : 157
% 0.46/0.66  # Proof object clause steps            : 102
% 0.46/0.66  # Proof object formula steps           : 55
% 0.46/0.66  # Proof object conjectures             : 33
% 0.46/0.66  # Proof object clause conjectures      : 30
% 0.46/0.66  # Proof object formula conjectures     : 3
% 0.46/0.66  # Proof object initial clauses used    : 41
% 0.46/0.66  # Proof object initial formulas used   : 28
% 0.46/0.66  # Proof object generating inferences   : 50
% 0.46/0.66  # Proof object simplifying inferences  : 98
% 0.46/0.66  # Training examples: 0 positive, 0 negative
% 0.46/0.66  # Parsed axioms                        : 32
% 0.46/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.66  # Initial clauses                      : 62
% 0.46/0.66  # Removed in clause preprocessing      : 5
% 0.46/0.66  # Initial clauses in saturation        : 57
% 0.46/0.66  # Processed clauses                    : 3480
% 0.46/0.66  # ...of these trivial                  : 23
% 0.46/0.66  # ...subsumed                          : 2462
% 0.46/0.66  # ...remaining for further processing  : 995
% 0.46/0.66  # Other redundant clauses eliminated   : 116
% 0.46/0.66  # Clauses deleted for lack of memory   : 0
% 0.46/0.66  # Backward-subsumed                    : 70
% 0.46/0.66  # Backward-rewritten                   : 248
% 0.46/0.66  # Generated clauses                    : 19358
% 0.46/0.66  # ...of the previous two non-trivial   : 17151
% 0.46/0.66  # Contextual simplify-reflections      : 96
% 0.46/0.66  # Paramodulations                      : 19242
% 0.46/0.66  # Factorizations                       : 0
% 0.46/0.66  # Equation resolutions                 : 116
% 0.46/0.66  # Propositional unsat checks           : 0
% 0.46/0.66  #    Propositional check models        : 0
% 0.46/0.66  #    Propositional check unsatisfiable : 0
% 0.46/0.66  #    Propositional clauses             : 0
% 0.46/0.66  #    Propositional clauses after purity: 0
% 0.46/0.66  #    Propositional unsat core size     : 0
% 0.46/0.66  #    Propositional preprocessing time  : 0.000
% 0.46/0.66  #    Propositional encoding time       : 0.000
% 0.46/0.66  #    Propositional solver time         : 0.000
% 0.46/0.66  #    Success case prop preproc time    : 0.000
% 0.46/0.66  #    Success case prop encoding time   : 0.000
% 0.46/0.66  #    Success case prop solver time     : 0.000
% 0.46/0.66  # Current number of processed clauses  : 617
% 0.46/0.66  #    Positive orientable unit clauses  : 52
% 0.46/0.66  #    Positive unorientable unit clauses: 0
% 0.46/0.66  #    Negative unit clauses             : 1
% 0.46/0.66  #    Non-unit-clauses                  : 564
% 0.46/0.66  # Current number of unprocessed clauses: 13665
% 0.46/0.66  # ...number of literals in the above   : 62974
% 0.46/0.66  # Current number of archived formulas  : 0
% 0.46/0.66  # Current number of archived clauses   : 373
% 0.46/0.66  # Clause-clause subsumption calls (NU) : 204151
% 0.46/0.66  # Rec. Clause-clause subsumption calls : 91343
% 0.46/0.66  # Non-unit clause-clause subsumptions  : 2189
% 0.46/0.66  # Unit Clause-clause subsumption calls : 396
% 0.46/0.66  # Rewrite failures with RHS unbound    : 0
% 0.46/0.66  # BW rewrite match attempts            : 84
% 0.46/0.66  # BW rewrite match successes           : 13
% 0.46/0.66  # Condensation attempts                : 0
% 0.46/0.66  # Condensation successes               : 0
% 0.46/0.66  # Termbank termtop insertions          : 245868
% 0.46/0.66  
% 0.46/0.66  # -------------------------------------------------
% 0.46/0.66  # User time                : 0.304 s
% 0.46/0.66  # System time              : 0.013 s
% 0.46/0.66  # Total time               : 0.317 s
% 0.46/0.66  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
