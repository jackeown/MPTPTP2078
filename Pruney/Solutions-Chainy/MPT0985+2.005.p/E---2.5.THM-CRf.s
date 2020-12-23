%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:33 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  178 (3164 expanded)
%              Number of clauses        :  125 (1407 expanded)
%              Number of leaves         :   27 ( 799 expanded)
%              Depth                    :   36
%              Number of atoms          :  499 (10492 expanded)
%              Number of equality atoms :  161 (2450 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(t177_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v2_funct_1(X1)
            & r1_tarski(X2,k1_relat_1(X1)) )
         => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc11_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(fc14_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ( v1_xboole_0(k4_relat_1(X1))
        & v1_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(c_0_27,negated_conjecture,(
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

fof(c_0_28,plain,(
    ! [X47,X48,X49] :
      ( ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k2_relset_1(X47,X48,X49) = k2_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_29,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

fof(c_0_30,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | v1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_31,plain,(
    ! [X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_32,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X41,X42,X43] :
      ( ( v4_relat_1(X43,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v5_relat_1(X43,X42)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(pm,[status(thm)],[c_0_35,c_0_33])).

fof(c_0_41,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v4_relat_1(X30,X29)
      | X30 = k7_relat_1(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_42,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_44,plain,(
    ! [X15] : m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_45,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_46,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | k2_relat_1(k7_relat_1(X28,X27)) = k9_relat_1(X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_47,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v4_relat_1(esk4_0,k1_relat_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_49,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_53,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k9_relat_1(X26,k1_relat_1(X26)) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_54,plain,(
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

fof(c_0_55,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ v2_funct_1(X35)
      | ~ r1_tarski(X36,k1_relat_1(X35))
      | k9_relat_1(k2_funct_1(X35),k9_relat_1(X35,X36)) = X36 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).

cnf(c_0_56,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_48]),c_0_40])])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_60,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_62,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_63,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,plain,
    ( k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_relat_1(esk4_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56,c_0_57]),c_0_38]),c_0_40])])).

cnf(c_0_67,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(pm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,plain,
    ( v4_relat_1(k2_zfmisc_1(X1,X2),X1) ),
    inference(pm,[status(thm)],[c_0_42,c_0_59])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_35,c_0_59])).

fof(c_0_72,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_73,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(pm,[status(thm)],[c_0_61,c_0_59])).

cnf(c_0_74,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( k9_relat_1(k2_funct_1(X1),k2_relat_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk4_0),esk3_0) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_39]),c_0_40]),c_0_68])])).

fof(c_0_77,plain,(
    ! [X34] :
      ( ( v1_relat_1(k2_funct_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( v1_funct_1(k2_funct_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_78,plain,
    ( v4_relat_1(k1_xboole_0,X1)
    | X2 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_80,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = k1_relat_1(esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_38]),c_0_76]),c_0_67]),c_0_39]),c_0_40])])).

cnf(c_0_83,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

fof(c_0_84,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v2_funct_1(X33)
      | k2_funct_1(X33) = k4_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_85,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_86,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1) ),
    inference(pm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_33,c_0_70])).

cnf(c_0_89,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_90,plain,(
    ! [X24] :
      ( ~ v1_xboole_0(X24)
      | v1_xboole_0(k2_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82,c_0_83]),c_0_39]),c_0_40])])).

cnf(c_0_92,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_85]),c_0_86])])).

cnf(c_0_94,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_87,c_0_81])).

fof(c_0_95,plain,(
    ! [X25] :
      ( ( v1_xboole_0(k4_relat_1(X25))
        | ~ v1_xboole_0(X25) )
      & ( v1_relat_1(k4_relat_1(X25))
        | ~ v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_relat_1])])])).

cnf(c_0_96,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61,c_0_88]),c_0_89])])).

cnf(c_0_97,plain,
    ( v1_xboole_0(k2_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk4_0)) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91,c_0_92]),c_0_67]),c_0_39]),c_0_40])])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_93,c_0_94]),c_0_93]),c_0_89])])).

cnf(c_0_100,plain,
    ( v1_xboole_0(k4_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_102,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_96,c_0_74])).

cnf(c_0_104,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_105,plain,(
    ! [X16,X17] :
      ( ~ v1_xboole_0(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_xboole_0(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_106,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_107,plain,(
    ! [X44,X45,X46] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k1_relset_1(X44,X45,X46) = k1_relat_1(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_97,c_0_38])).

cnf(c_0_109,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(k4_relat_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_110,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ r1_tarski(k2_funct_1(esk4_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(pm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 = X1
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(pm,[status(thm)],[c_0_80,c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( k9_relat_1(k4_relat_1(esk4_0),esk3_0) = k1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_92]),c_0_67]),c_0_39]),c_0_40])])).

cnf(c_0_114,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56,c_0_93]),c_0_104]),c_0_86])])).

cnf(c_0_115,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_33,c_0_106])).

fof(c_0_117,plain,(
    ! [X50,X51,X52] :
      ( ( ~ v1_funct_2(X52,X50,X51)
        | X50 = k1_relset_1(X50,X51,X52)
        | X51 = k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X50 != k1_relset_1(X50,X51,X52)
        | v1_funct_2(X52,X50,X51)
        | X51 = k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( ~ v1_funct_2(X52,X50,X51)
        | X50 = k1_relset_1(X50,X51,X52)
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X50 != k1_relset_1(X50,X51,X52)
        | v1_funct_2(X52,X50,X51)
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( ~ v1_funct_2(X52,X50,X51)
        | X52 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( X52 != k1_xboole_0
        | v1_funct_2(X52,X50,X51)
        | X50 = k1_xboole_0
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_118,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_119,negated_conjecture,
    ( X1 = esk3_0
    | ~ v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_94,c_0_108])).

cnf(c_0_120,negated_conjecture,
    ( v1_xboole_0(k1_relat_1(esk4_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109,c_0_110]),c_0_89])])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_111,c_0_81])).

cnf(c_0_122,negated_conjecture,
    ( esk4_0 = X1
    | esk3_0 != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_112,c_0_81])).

cnf(c_0_123,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_113,c_0_110]),c_0_114])).

cnf(c_0_124,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115,c_0_116]),c_0_89])])).

cnf(c_0_125,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_126,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(pm,[status(thm)],[c_0_118,c_0_33])).

cnf(c_0_127,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_128,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_129,negated_conjecture,
    ( ~ v1_funct_2(k4_relat_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_121,c_0_92]),c_0_67]),c_0_39])]),c_0_40])])).

cnf(c_0_130,negated_conjecture,
    ( k4_relat_1(X1) = esk4_0
    | esk3_0 != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_122,c_0_100])).

cnf(c_0_131,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_99,c_0_108])).

cnf(c_0_132,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_133,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_134,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125,c_0_33]),c_0_126]),c_0_127])])).

cnf(c_0_135,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_128,c_0_124])).

cnf(c_0_136,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(esk4_0,esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_137,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_131,c_0_124])).

cnf(c_0_138,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_132,c_0_133]),c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_139,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_138,c_0_139])).

fof(c_0_142,plain,(
    ! [X31] :
      ( ~ v1_xboole_0(X31)
      | v1_funct_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_143,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_144,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_142])).

cnf(c_0_145,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_146,plain,
    ( k1_relset_1(X1,X2,k2_zfmisc_1(X1,X2)) = k1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_118,c_0_59])).

cnf(c_0_147,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_xboole_0(k4_relat_1(esk4_0))
    | ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_145,c_0_92]),c_0_67]),c_0_39]),c_0_40])])).

cnf(c_0_148,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_149,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_relset_1(X1,X2,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_146,c_0_106])).

cnf(c_0_150,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_151,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_147,c_0_130])).

cnf(c_0_152,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115,c_0_88]),c_0_89])])).

cnf(c_0_153,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_148,c_0_106])).

cnf(c_0_154,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_149,c_0_106]),c_0_150])).

cnf(c_0_155,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_156,negated_conjecture,
    ( ~ v1_funct_2(X1,esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_121,c_0_94])).

cnf(c_0_157,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X2,X1)
    | k1_xboole_0 != X2 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_153,c_0_154]),c_0_59])])).

cnf(c_0_158,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_155,c_0_137])).

cnf(c_0_159,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_156,c_0_157]),c_0_89])]),c_0_158])).

cnf(c_0_160,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_159,c_0_144])).

cnf(c_0_161,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_xboole_0(k4_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_160,c_0_92]),c_0_67]),c_0_39]),c_0_40])])).

cnf(c_0_162,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_163,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(pm,[status(thm)],[c_0_161,c_0_130])).

cnf(c_0_164,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_162,c_0_33]),c_0_126]),c_0_127])])).

cnf(c_0_165,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_163,c_0_152])).

cnf(c_0_166,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(sr,[status(thm)],[c_0_164,c_0_165])).

cnf(c_0_167,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_37,c_0_64])).

cnf(c_0_168,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_166])).

cnf(c_0_169,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_132,c_0_64])).

cnf(c_0_170,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_167,c_0_168]),c_0_38]),c_0_67]),c_0_39]),c_0_40])])).

cnf(c_0_171,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_169,c_0_91]),c_0_38]),c_0_67]),c_0_39]),c_0_40])])).

cnf(c_0_172,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_101,c_0_170])).

cnf(c_0_173,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_171,c_0_166])).

cnf(c_0_174,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_172,c_0_173])).

cnf(c_0_175,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_174,c_0_83]),c_0_39]),c_0_40])])).

cnf(c_0_176,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_177,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_175,c_0_176]),c_0_39]),c_0_40])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.37/0.54  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.37/0.54  # and selection function NoSelection.
% 0.37/0.54  #
% 0.37/0.54  # Preprocessing time       : 0.029 s
% 0.37/0.54  
% 0.37/0.54  # Proof found!
% 0.37/0.54  # SZS status Theorem
% 0.37/0.54  # SZS output start CNFRefutation
% 0.37/0.54  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.37/0.54  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.37/0.54  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.37/0.54  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.37/0.54  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.37/0.54  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.37/0.54  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.37/0.54  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.37/0.54  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.37/0.54  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.54  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.37/0.54  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.37/0.54  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.37/0.54  fof(t177_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 0.37/0.54  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.37/0.54  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.37/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.54  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.37/0.54  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.37/0.54  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.37/0.54  fof(fc11_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 0.37/0.54  fof(fc14_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>(v1_xboole_0(k4_relat_1(X1))&v1_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 0.37/0.54  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.37/0.54  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.37/0.54  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.37/0.54  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.37/0.54  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.37/0.54  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.37/0.54  fof(c_0_28, plain, ![X47, X48, X49]:(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k2_relset_1(X47,X48,X49)=k2_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.37/0.54  fof(c_0_29, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v2_funct_1(esk4_0)&k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.37/0.54  fof(c_0_30, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.37/0.54  fof(c_0_31, plain, ![X53]:(((v1_funct_1(X53)|(~v1_relat_1(X53)|~v1_funct_1(X53)))&(v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))|(~v1_relat_1(X53)|~v1_funct_1(X53))))&(m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))|(~v1_relat_1(X53)|~v1_funct_1(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.37/0.54  cnf(c_0_32, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.37/0.54  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_34, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_35, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.37/0.54  fof(c_0_36, plain, ![X41, X42, X43]:((v4_relat_1(X43,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))&(v5_relat_1(X43,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.37/0.54  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.54  cnf(c_0_38, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.37/0.54  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk4_0)), inference(pm,[status(thm)],[c_0_35, c_0_33])).
% 0.37/0.54  fof(c_0_41, plain, ![X29, X30]:(~v1_relat_1(X30)|~v4_relat_1(X30,X29)|X30=k7_relat_1(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.37/0.54  cnf(c_0_42, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.37/0.54  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.37/0.54  fof(c_0_44, plain, ![X15]:m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.37/0.54  fof(c_0_45, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.37/0.54  fof(c_0_46, plain, ![X27, X28]:(~v1_relat_1(X28)|k2_relat_1(k7_relat_1(X28,X27))=k9_relat_1(X28,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.37/0.54  cnf(c_0_47, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.37/0.54  cnf(c_0_48, negated_conjecture, (v4_relat_1(esk4_0,k1_relat_1(esk4_0))), inference(pm,[status(thm)],[c_0_42, c_0_43])).
% 0.37/0.54  fof(c_0_49, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.54  cnf(c_0_50, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.54  cnf(c_0_51, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.37/0.54  fof(c_0_52, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|~v1_xboole_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.37/0.54  fof(c_0_53, plain, ![X26]:(~v1_relat_1(X26)|k9_relat_1(X26,k1_relat_1(X26))=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.37/0.54  fof(c_0_54, plain, ![X37]:((k2_relat_1(X37)=k1_relat_1(k2_funct_1(X37))|~v2_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(k1_relat_1(X37)=k2_relat_1(k2_funct_1(X37))|~v2_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.37/0.54  fof(c_0_55, plain, ![X35, X36]:(~v1_relat_1(X35)|~v1_funct_1(X35)|(~v2_funct_1(X35)|~r1_tarski(X36,k1_relat_1(X35))|k9_relat_1(k2_funct_1(X35),k9_relat_1(X35,X36))=X36)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).
% 0.37/0.54  cnf(c_0_56, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.37/0.54  cnf(c_0_57, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_48]), c_0_40])])).
% 0.37/0.54  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.37/0.54  cnf(c_0_59, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 0.37/0.54  fof(c_0_60, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.37/0.54  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.37/0.54  fof(c_0_62, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.37/0.54  cnf(c_0_63, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.37/0.54  cnf(c_0_64, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.37/0.54  cnf(c_0_65, plain, (k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.37/0.54  cnf(c_0_66, negated_conjecture, (k9_relat_1(esk4_0,k1_relat_1(esk4_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56, c_0_57]), c_0_38]), c_0_40])])).
% 0.37/0.54  cnf(c_0_67, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(pm,[status(thm)],[c_0_58, c_0_59])).
% 0.37/0.54  cnf(c_0_69, plain, (v4_relat_1(k2_zfmisc_1(X1,X2),X1)), inference(pm,[status(thm)],[c_0_42, c_0_59])).
% 0.37/0.54  cnf(c_0_70, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.37/0.54  cnf(c_0_71, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_35, c_0_59])).
% 0.37/0.54  fof(c_0_72, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.54  cnf(c_0_73, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(pm,[status(thm)],[c_0_61, c_0_59])).
% 0.37/0.54  cnf(c_0_74, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.37/0.54  cnf(c_0_75, plain, (k9_relat_1(k2_funct_1(X1),k2_relat_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_63, c_0_64])).
% 0.37/0.54  cnf(c_0_76, negated_conjecture, (k9_relat_1(k2_funct_1(esk4_0),esk3_0)=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_39]), c_0_40]), c_0_68])])).
% 0.37/0.54  fof(c_0_77, plain, ![X34]:((v1_relat_1(k2_funct_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(v1_funct_1(k2_funct_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.37/0.54  cnf(c_0_78, plain, (v4_relat_1(k1_xboole_0,X1)|X2!=k1_xboole_0), inference(pm,[status(thm)],[c_0_69, c_0_70])).
% 0.37/0.54  cnf(c_0_79, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_71, c_0_70])).
% 0.37/0.54  cnf(c_0_80, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.37/0.54  cnf(c_0_81, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_73, c_0_74])).
% 0.37/0.54  cnf(c_0_82, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=k1_relat_1(esk4_0)|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_38]), c_0_76]), c_0_67]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_83, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.37/0.54  fof(c_0_84, plain, ![X33]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(~v2_funct_1(X33)|k2_funct_1(X33)=k4_relat_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.37/0.54  cnf(c_0_85, plain, (v4_relat_1(k1_xboole_0,X1)), inference(er,[status(thm)],[c_0_78])).
% 0.37/0.54  cnf(c_0_86, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_79])).
% 0.37/0.54  cnf(c_0_87, plain, (X1=X2|~v1_xboole_0(X1)|~r1_tarski(X2,X1)), inference(pm,[status(thm)],[c_0_80, c_0_81])).
% 0.37/0.54  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_33, c_0_70])).
% 0.37/0.54  cnf(c_0_89, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.37/0.54  fof(c_0_90, plain, ![X24]:(~v1_xboole_0(X24)|v1_xboole_0(k2_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc11_relat_1])])).
% 0.37/0.54  cnf(c_0_91, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_82, c_0_83]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_92, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.37/0.54  cnf(c_0_93, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_85]), c_0_86])])).
% 0.37/0.54  cnf(c_0_94, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_87, c_0_81])).
% 0.37/0.54  fof(c_0_95, plain, ![X25]:((v1_xboole_0(k4_relat_1(X25))|~v1_xboole_0(X25))&(v1_relat_1(k4_relat_1(X25))|~v1_xboole_0(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_relat_1])])])).
% 0.37/0.54  cnf(c_0_96, negated_conjecture, (esk3_0!=k1_xboole_0|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61, c_0_88]), c_0_89])])).
% 0.37/0.54  cnf(c_0_97, plain, (v1_xboole_0(k2_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.37/0.54  cnf(c_0_98, negated_conjecture, (k2_relat_1(k4_relat_1(esk4_0))=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91, c_0_92]), c_0_67]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_99, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_93, c_0_94]), c_0_93]), c_0_89])])).
% 0.37/0.54  cnf(c_0_100, plain, (v1_xboole_0(k4_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.37/0.54  cnf(c_0_101, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_102, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.37/0.54  cnf(c_0_103, negated_conjecture, (r1_tarski(esk4_0,X1)|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_96, c_0_74])).
% 0.37/0.54  cnf(c_0_104, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.37/0.54  fof(c_0_105, plain, ![X16, X17]:(~v1_xboole_0(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_xboole_0(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.37/0.54  cnf(c_0_106, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.37/0.54  fof(c_0_107, plain, ![X44, X45, X46]:(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k1_relset_1(X44,X45,X46)=k1_relat_1(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.37/0.54  cnf(c_0_108, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_97, c_0_38])).
% 0.37/0.54  cnf(c_0_109, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~v1_xboole_0(k4_relat_1(esk4_0))), inference(pm,[status(thm)],[c_0_97, c_0_98])).
% 0.37/0.54  cnf(c_0_110, plain, (k4_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_99, c_0_100])).
% 0.37/0.54  cnf(c_0_111, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~r1_tarski(k2_funct_1(esk4_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(pm,[status(thm)],[c_0_101, c_0_102])).
% 0.37/0.54  cnf(c_0_112, negated_conjecture, (esk4_0=X1|esk3_0!=k1_xboole_0|~r1_tarski(X1,esk4_0)), inference(pm,[status(thm)],[c_0_80, c_0_103])).
% 0.37/0.54  cnf(c_0_113, negated_conjecture, (k9_relat_1(k4_relat_1(esk4_0),esk3_0)=k1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_92]), c_0_67]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_114, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56, c_0_93]), c_0_104]), c_0_86])])).
% 0.37/0.54  cnf(c_0_115, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.37/0.54  cnf(c_0_116, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_33, c_0_106])).
% 0.37/0.54  fof(c_0_117, plain, ![X50, X51, X52]:((((~v1_funct_2(X52,X50,X51)|X50=k1_relset_1(X50,X51,X52)|X51=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X50!=k1_relset_1(X50,X51,X52)|v1_funct_2(X52,X50,X51)|X51=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&((~v1_funct_2(X52,X50,X51)|X50=k1_relset_1(X50,X51,X52)|X50!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X50!=k1_relset_1(X50,X51,X52)|v1_funct_2(X52,X50,X51)|X50!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))))&((~v1_funct_2(X52,X50,X51)|X52=k1_xboole_0|X50=k1_xboole_0|X51!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))&(X52!=k1_xboole_0|v1_funct_2(X52,X50,X51)|X50=k1_xboole_0|X51!=k1_xboole_0|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.37/0.54  cnf(c_0_118, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.37/0.54  cnf(c_0_119, negated_conjecture, (X1=esk3_0|~v1_xboole_0(esk4_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_94, c_0_108])).
% 0.37/0.54  cnf(c_0_120, negated_conjecture, (v1_xboole_0(k1_relat_1(esk4_0))|~v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109, c_0_110]), c_0_89])])).
% 0.37/0.54  cnf(c_0_121, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_111, c_0_81])).
% 0.37/0.54  cnf(c_0_122, negated_conjecture, (esk4_0=X1|esk3_0!=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_112, c_0_81])).
% 0.37/0.54  cnf(c_0_123, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_113, c_0_110]), c_0_114])).
% 0.37/0.54  cnf(c_0_124, negated_conjecture, (v1_xboole_0(esk4_0)|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115, c_0_116]), c_0_89])])).
% 0.37/0.54  cnf(c_0_125, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.37/0.54  cnf(c_0_126, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(pm,[status(thm)],[c_0_118, c_0_33])).
% 0.37/0.54  cnf(c_0_127, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_128, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_119, c_0_120])).
% 0.37/0.54  cnf(c_0_129, negated_conjecture, (~v1_funct_2(k4_relat_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_121, c_0_92]), c_0_67]), c_0_39])]), c_0_40])])).
% 0.37/0.54  cnf(c_0_130, negated_conjecture, (k4_relat_1(X1)=esk4_0|esk3_0!=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_122, c_0_100])).
% 0.37/0.54  cnf(c_0_131, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_99, c_0_108])).
% 0.37/0.54  cnf(c_0_132, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.37/0.54  cnf(c_0_133, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_123, c_0_124])).
% 0.37/0.54  cnf(c_0_134, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125, c_0_33]), c_0_126]), c_0_127])])).
% 0.37/0.54  cnf(c_0_135, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0|esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_128, c_0_124])).
% 0.37/0.54  cnf(c_0_136, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(esk4_0,esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_129, c_0_130])).
% 0.37/0.54  cnf(c_0_137, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_131, c_0_124])).
% 0.37/0.54  cnf(c_0_138, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_132, c_0_133]), c_0_38]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_139, negated_conjecture, (esk3_0=esk2_0|esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_134, c_0_135])).
% 0.37/0.54  cnf(c_0_140, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_136, c_0_137])).
% 0.37/0.54  cnf(c_0_141, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_138, c_0_139])).
% 0.37/0.54  fof(c_0_142, plain, ![X31]:(~v1_xboole_0(X31)|v1_funct_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.37/0.54  cnf(c_0_143, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_140, c_0_141])).
% 0.37/0.54  cnf(c_0_144, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_142])).
% 0.37/0.54  cnf(c_0_145, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_143, c_0_144])).
% 0.37/0.54  cnf(c_0_146, plain, (k1_relset_1(X1,X2,k2_zfmisc_1(X1,X2))=k1_relat_1(k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_118, c_0_59])).
% 0.37/0.54  cnf(c_0_147, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_xboole_0(k4_relat_1(esk4_0))|~v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_145, c_0_92]), c_0_67]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_148, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.37/0.54  cnf(c_0_149, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=k1_relset_1(X1,X2,k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_146, c_0_106])).
% 0.37/0.54  cnf(c_0_150, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.37/0.54  cnf(c_0_151, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_147, c_0_130])).
% 0.37/0.54  cnf(c_0_152, negated_conjecture, (v1_xboole_0(esk4_0)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115, c_0_88]), c_0_89])])).
% 0.37/0.54  cnf(c_0_153, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|X3!=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_148, c_0_106])).
% 0.37/0.54  cnf(c_0_154, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_149, c_0_106]), c_0_150])).
% 0.37/0.54  cnf(c_0_155, negated_conjecture, (esk3_0!=k1_xboole_0|esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_151, c_0_152])).
% 0.37/0.54  cnf(c_0_156, negated_conjecture, (~v1_funct_2(X1,esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_121, c_0_94])).
% 0.37/0.54  cnf(c_0_157, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X2,X1)|k1_xboole_0!=X2), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_153, c_0_154]), c_0_59])])).
% 0.37/0.54  cnf(c_0_158, negated_conjecture, (esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_155, c_0_137])).
% 0.37/0.54  cnf(c_0_159, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_156, c_0_157]), c_0_89])]), c_0_158])).
% 0.37/0.54  cnf(c_0_160, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_159, c_0_144])).
% 0.37/0.54  cnf(c_0_161, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_xboole_0(k4_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_160, c_0_92]), c_0_67]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_162, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.37/0.54  cnf(c_0_163, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(pm,[status(thm)],[c_0_161, c_0_130])).
% 0.37/0.54  cnf(c_0_164, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_162, c_0_33]), c_0_126]), c_0_127])])).
% 0.37/0.54  cnf(c_0_165, negated_conjecture, (esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_163, c_0_152])).
% 0.37/0.54  cnf(c_0_166, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(sr,[status(thm)],[c_0_164, c_0_165])).
% 0.37/0.54  cnf(c_0_167, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_37, c_0_64])).
% 0.37/0.54  cnf(c_0_168, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=esk2_0), inference(rw,[status(thm)],[c_0_91, c_0_166])).
% 0.37/0.54  cnf(c_0_169, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_132, c_0_64])).
% 0.37/0.54  cnf(c_0_170, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_167, c_0_168]), c_0_38]), c_0_67]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_171, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_169, c_0_91]), c_0_38]), c_0_67]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_172, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_101, c_0_170])).
% 0.37/0.54  cnf(c_0_173, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(rw,[status(thm)],[c_0_171, c_0_166])).
% 0.37/0.54  cnf(c_0_174, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_172, c_0_173])).
% 0.37/0.54  cnf(c_0_175, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_174, c_0_83]), c_0_39]), c_0_40])])).
% 0.37/0.54  cnf(c_0_176, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.37/0.54  cnf(c_0_177, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_175, c_0_176]), c_0_39]), c_0_40])]), ['proof']).
% 0.37/0.54  # SZS output end CNFRefutation
% 0.37/0.54  # Proof object total steps             : 178
% 0.37/0.54  # Proof object clause steps            : 125
% 0.37/0.54  # Proof object formula steps           : 53
% 0.37/0.54  # Proof object conjectures             : 71
% 0.37/0.54  # Proof object clause conjectures      : 68
% 0.37/0.54  # Proof object formula conjectures     : 3
% 0.37/0.54  # Proof object initial clauses used    : 39
% 0.37/0.54  # Proof object initial formulas used   : 27
% 0.37/0.54  # Proof object generating inferences   : 82
% 0.37/0.54  # Proof object simplifying inferences  : 96
% 0.37/0.54  # Training examples: 0 positive, 0 negative
% 0.37/0.54  # Parsed axioms                        : 29
% 0.37/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.54  # Initial clauses                      : 55
% 0.37/0.54  # Removed in clause preprocessing      : 4
% 0.37/0.54  # Initial clauses in saturation        : 51
% 0.37/0.54  # Processed clauses                    : 2517
% 0.37/0.54  # ...of these trivial                  : 5
% 0.37/0.54  # ...subsumed                          : 1816
% 0.37/0.54  # ...remaining for further processing  : 696
% 0.37/0.54  # Other redundant clauses eliminated   : 0
% 0.37/0.54  # Clauses deleted for lack of memory   : 0
% 0.37/0.54  # Backward-subsumed                    : 103
% 0.37/0.54  # Backward-rewritten                   : 107
% 0.37/0.54  # Generated clauses                    : 11523
% 0.37/0.54  # ...of the previous two non-trivial   : 10725
% 0.37/0.54  # Contextual simplify-reflections      : 0
% 0.37/0.54  # Paramodulations                      : 11507
% 0.37/0.54  # Factorizations                       : 0
% 0.37/0.54  # Equation resolutions                 : 15
% 0.37/0.54  # Propositional unsat checks           : 0
% 0.37/0.54  #    Propositional check models        : 0
% 0.37/0.54  #    Propositional check unsatisfiable : 0
% 0.37/0.54  #    Propositional clauses             : 0
% 0.37/0.54  #    Propositional clauses after purity: 0
% 0.37/0.54  #    Propositional unsat core size     : 0
% 0.37/0.54  #    Propositional preprocessing time  : 0.000
% 0.37/0.54  #    Propositional encoding time       : 0.000
% 0.37/0.54  #    Propositional solver time         : 0.000
% 0.37/0.54  #    Success case prop preproc time    : 0.000
% 0.37/0.54  #    Success case prop encoding time   : 0.000
% 0.37/0.54  #    Success case prop solver time     : 0.000
% 0.37/0.54  # Current number of processed clauses  : 485
% 0.37/0.54  #    Positive orientable unit clauses  : 35
% 0.37/0.54  #    Positive unorientable unit clauses: 0
% 0.37/0.54  #    Negative unit clauses             : 7
% 0.37/0.54  #    Non-unit-clauses                  : 443
% 0.37/0.54  # Current number of unprocessed clauses: 8172
% 0.37/0.54  # ...number of literals in the above   : 38958
% 0.37/0.54  # Current number of archived formulas  : 0
% 0.37/0.54  # Current number of archived clauses   : 212
% 0.37/0.54  # Clause-clause subsumption calls (NU) : 34562
% 0.37/0.54  # Rec. Clause-clause subsumption calls : 21409
% 0.37/0.54  # Non-unit clause-clause subsumptions  : 1275
% 0.37/0.54  # Unit Clause-clause subsumption calls : 1463
% 0.37/0.54  # Rewrite failures with RHS unbound    : 0
% 0.37/0.54  # BW rewrite match attempts            : 14
% 0.37/0.54  # BW rewrite match successes           : 7
% 0.37/0.54  # Condensation attempts                : 0
% 0.37/0.54  # Condensation successes               : 0
% 0.37/0.54  # Termbank termtop insertions          : 78216
% 0.37/0.55  
% 0.37/0.55  # -------------------------------------------------
% 0.37/0.55  # User time                : 0.189 s
% 0.37/0.55  # System time              : 0.011 s
% 0.37/0.55  # Total time               : 0.200 s
% 0.37/0.55  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
