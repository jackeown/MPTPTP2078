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
% DateTime   : Thu Dec  3 11:02:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 714 expanded)
%              Number of clauses        :   77 ( 299 expanded)
%              Number of leaves         :   19 ( 183 expanded)
%              Depth                    :   29
%              Number of atoms          :  387 (3004 expanded)
%              Number of equality atoms :  125 ( 703 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(c_0_19,plain,(
    ! [X39] : m1_subset_1(k6_relat_1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X26] :
      ( ( k1_relat_1(X26) != k1_xboole_0
        | k2_relat_1(X26) = k1_xboole_0
        | ~ v1_relat_1(X26) )
      & ( k2_relat_1(X26) != k1_xboole_0
        | k1_relat_1(X26) = k1_xboole_0
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_31,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_32,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk2_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk3_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk3_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk3_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk4_2(X21,X22),esk3_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_33,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(pm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( k2_relat_1(k6_relat_1(X1)) = k1_xboole_0
    | k1_relat_1(k6_relat_1(X1)) != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_42,plain,
    ( X1 != k2_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X2)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k2_relat_1(k6_relat_1(X1)) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_44,plain,
    ( k1_xboole_0 != X1
    | X2 != k1_xboole_0
    | ~ r2_hidden(k4_tarski(X3,X4),k6_relat_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_45,plain,
    ( k1_xboole_0 != X1
    | X2 != k1_xboole_0
    | ~ r2_hidden(k4_tarski(X3,X4),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_44,c_0_40])).

cnf(c_0_46,plain,
    ( k1_xboole_0 != X1
    | ~ r2_hidden(k4_tarski(X2,X3),k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_47,plain,
    ( k6_relat_1(X1) != k1_xboole_0
    | X1 != k1_xboole_0
    | ~ r2_hidden(k4_tarski(X2,X3),k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_46,c_0_36])).

fof(c_0_48,negated_conjecture,(
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

cnf(c_0_49,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(k4_tarski(X2,X3),k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_47,c_0_40])).

fof(c_0_50,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_51,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v2_funct_1(esk7_0)
    & k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0
    & ( ~ v1_funct_1(k2_funct_1(esk7_0))
      | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
      | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_55,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_56,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_60,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_37,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_64,plain,
    ( X1 = k2_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( X1 = esk6_0
    | X1 != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(pm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_67,plain,(
    ! [X44,X45] :
      ( ( v1_funct_1(X45)
        | ~ r1_tarski(k2_relat_1(X45),X44)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( v1_funct_2(X45,k1_relat_1(X45),X44)
        | ~ r1_tarski(k2_relat_1(X45),X44)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X45),X44)))
        | ~ r1_tarski(k2_relat_1(X45),X44)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_68,plain,(
    ! [X43] :
      ( ( v1_funct_1(X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( v1_funct_2(X43,k1_relat_1(X43),k2_relat_1(X43))
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X43),k2_relat_1(X43))))
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_69,plain,(
    ! [X27] :
      ( ( v1_relat_1(k2_funct_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_1(k2_funct_1(X27))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | X1 != k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk7_0),X1,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(pm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_74,plain,(
    ! [X28] :
      ( ( k2_relat_1(X28) = k1_relat_1(k2_funct_1(X28))
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( k1_relat_1(X28) = k2_relat_1(k2_funct_1(X28))
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk7_0)) != k1_xboole_0
    | esk6_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0))
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk7_0)),esk5_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(pm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_72,c_0_62])).

cnf(c_0_77,plain,
    ( k2_relat_1(k2_funct_1(X1)) = k1_xboole_0
    | k1_relat_1(k2_funct_1(X1)) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_33,c_0_73])).

cnf(c_0_78,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_79,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_80,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk7_0)) != k1_xboole_0
    | esk6_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(esk7_0)),esk5_0)
    | ~ v1_xboole_0(esk7_0) ),
    inference(pm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( k2_relat_1(k2_funct_1(X1)) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_85,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(pm,[status(thm)],[c_0_26,c_0_57])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk7_0)) != k1_xboole_0
    | esk6_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_63]),c_0_83]),c_0_84]),c_0_85])])).

cnf(c_0_87,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_88,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk7_0)) != k1_xboole_0
    | esk6_0 != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_87]),c_0_84]),c_0_85])])).

fof(c_0_90,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X42 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X42 != k1_xboole_0
        | v1_funct_2(X42,X40,X41)
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_91,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk7_0)) != k1_xboole_0
    | esk6_0 != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89,c_0_73]),c_0_84]),c_0_85])])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk6_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_57,c_0_24])).

cnf(c_0_94,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(pm,[status(thm)],[c_0_91,c_0_57])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_97,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92,c_0_78]),c_0_63]),c_0_83]),c_0_84]),c_0_85])])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28,c_0_93]),c_0_30])])).

cnf(c_0_99,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_72,c_0_78])).

cnf(c_0_100,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94,c_0_57]),c_0_95]),c_0_96])])).

cnf(c_0_101,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(k2_funct_1(esk7_0)))))
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99,c_0_63]),c_0_83]),c_0_84]),c_0_85])])).

cnf(c_0_104,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_105,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_106,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_102,c_0_78])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_83]),c_0_84]),c_0_85])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk7_0),esk6_0,k2_relat_1(k2_funct_1(esk7_0)))
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106,c_0_63]),c_0_83]),c_0_84]),c_0_85])])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(pm,[status(thm)],[c_0_61,c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_108,c_0_104]),c_0_83]),c_0_84]),c_0_85])]),c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(pm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111,c_0_87]),c_0_84]),c_0_85])])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112,c_0_73]),c_0_84]),c_0_85])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.20/0.45  # and selection function NoSelection.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.029 s
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.20/0.45  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.45  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.45  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.45  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.20/0.45  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.45  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.45  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.45  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.45  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.45  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.45  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.45  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.45  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.45  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.45  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.45  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.45  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.45  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.45  fof(c_0_19, plain, ![X39]:m1_subset_1(k6_relat_1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.20/0.45  fof(c_0_20, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.45  fof(c_0_21, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.45  fof(c_0_22, plain, ![X13, X14]:(~v1_xboole_0(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.45  cnf(c_0_23, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_24, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  fof(c_0_25, plain, ![X26]:((k1_relat_1(X26)!=k1_xboole_0|k2_relat_1(X26)=k1_xboole_0|~v1_relat_1(X26))&(k2_relat_1(X26)!=k1_xboole_0|k1_relat_1(X26)=k1_xboole_0|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.20/0.45  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  fof(c_0_27, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.45  cnf(c_0_28, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.45  cnf(c_0_29, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k1_xboole_0))|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.45  cnf(c_0_30, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.45  fof(c_0_31, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.45  fof(c_0_32, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(esk2_3(X15,X16,X17),X17),X15)|X16!=k2_relat_1(X15))&(~r2_hidden(k4_tarski(X20,X19),X15)|r2_hidden(X19,X16)|X16!=k2_relat_1(X15)))&((~r2_hidden(esk3_2(X21,X22),X22)|~r2_hidden(k4_tarski(X24,esk3_2(X21,X22)),X21)|X22=k2_relat_1(X21))&(r2_hidden(esk3_2(X21,X22),X22)|r2_hidden(k4_tarski(esk4_2(X21,X22),esk3_2(X21,X22)),X21)|X22=k2_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.45  cnf(c_0_33, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  cnf(c_0_34, plain, (v1_relat_1(k6_relat_1(X1))), inference(pm,[status(thm)],[c_0_26, c_0_23])).
% 0.20/0.45  cnf(c_0_35, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.45  cnf(c_0_36, plain, (v1_xboole_0(k6_relat_1(X1))|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.20/0.45  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.45  cnf(c_0_38, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_39, plain, (k2_relat_1(k6_relat_1(X1))=k1_xboole_0|k1_relat_1(k6_relat_1(X1))!=k1_xboole_0), inference(pm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.45  cnf(c_0_40, plain, (k6_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.45  cnf(c_0_41, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.45  cnf(c_0_42, plain, (X1!=k2_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X2)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.45  cnf(c_0_43, plain, (k2_relat_1(k6_relat_1(X1))=k1_xboole_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.20/0.45  cnf(c_0_44, plain, (k1_xboole_0!=X1|X2!=k1_xboole_0|~r2_hidden(k4_tarski(X3,X4),k6_relat_1(X2))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.45  cnf(c_0_45, plain, (k1_xboole_0!=X1|X2!=k1_xboole_0|~r2_hidden(k4_tarski(X3,X4),k1_xboole_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_44, c_0_40])).
% 0.20/0.45  cnf(c_0_46, plain, (k1_xboole_0!=X1|~r2_hidden(k4_tarski(X2,X3),k1_xboole_0)|~v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.45  cnf(c_0_47, plain, (k6_relat_1(X1)!=k1_xboole_0|X1!=k1_xboole_0|~r2_hidden(k4_tarski(X2,X3),k1_xboole_0)), inference(pm,[status(thm)],[c_0_46, c_0_36])).
% 0.20/0.45  fof(c_0_48, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.20/0.45  cnf(c_0_49, plain, (X1!=k1_xboole_0|~r2_hidden(k4_tarski(X2,X3),k1_xboole_0)), inference(pm,[status(thm)],[c_0_47, c_0_40])).
% 0.20/0.45  fof(c_0_50, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k2_relset_1(X36,X37,X38)=k2_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.45  fof(c_0_51, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((v2_funct_1(esk7_0)&k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0)&(~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 0.20/0.45  cnf(c_0_52, plain, (~r2_hidden(k4_tarski(X1,X2),k1_xboole_0)), inference(er,[status(thm)],[c_0_49])).
% 0.20/0.45  cnf(c_0_53, plain, (r2_hidden(k4_tarski(esk2_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.45  cnf(c_0_55, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.45  cnf(c_0_56, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_58, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_59, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.20/0.45  cnf(c_0_60, plain, (X1=k2_relat_1(X2)|r2_hidden(esk3_2(X2,X1),X1)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_37, c_0_55])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_62, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk7_0)=esk6_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.20/0.45  cnf(c_0_64, plain, (X1=k2_relat_1(X2)|X1!=k1_xboole_0|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.45  cnf(c_0_65, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (X1=esk6_0|X1!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(pm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.45  fof(c_0_67, plain, ![X44, X45]:(((v1_funct_1(X45)|~r1_tarski(k2_relat_1(X45),X44)|(~v1_relat_1(X45)|~v1_funct_1(X45)))&(v1_funct_2(X45,k1_relat_1(X45),X44)|~r1_tarski(k2_relat_1(X45),X44)|(~v1_relat_1(X45)|~v1_funct_1(X45))))&(m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X45),X44)))|~r1_tarski(k2_relat_1(X45),X44)|(~v1_relat_1(X45)|~v1_funct_1(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.45  fof(c_0_68, plain, ![X43]:(((v1_funct_1(X43)|(~v1_relat_1(X43)|~v1_funct_1(X43)))&(v1_funct_2(X43,k1_relat_1(X43),k2_relat_1(X43))|(~v1_relat_1(X43)|~v1_funct_1(X43))))&(m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X43),k2_relat_1(X43))))|(~v1_relat_1(X43)|~v1_funct_1(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.45  fof(c_0_69, plain, ![X27]:((v1_relat_1(k2_funct_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(v1_funct_1(k2_funct_1(X27))|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.45  cnf(c_0_70, negated_conjecture, (esk6_0!=k1_xboole_0|X1!=k1_xboole_0|~v1_funct_2(k2_funct_1(esk7_0),X1,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk7_0)), inference(pm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.45  cnf(c_0_71, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.45  cnf(c_0_72, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.45  cnf(c_0_73, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.45  fof(c_0_74, plain, ![X28]:((k2_relat_1(X28)=k1_relat_1(k2_funct_1(X28))|~v2_funct_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(k1_relat_1(X28)=k2_relat_1(k2_funct_1(X28))|~v2_funct_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.45  cnf(c_0_75, negated_conjecture, (k1_relat_1(k2_funct_1(esk7_0))!=k1_xboole_0|esk6_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k2_relat_1(k2_funct_1(esk7_0)),esk5_0)|~v1_xboole_0(esk7_0)), inference(pm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.45  cnf(c_0_76, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_72, c_0_62])).
% 0.20/0.45  cnf(c_0_77, plain, (k2_relat_1(k2_funct_1(X1))=k1_xboole_0|k1_relat_1(k2_funct_1(X1))!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_33, c_0_73])).
% 0.20/0.45  cnf(c_0_78, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.45  fof(c_0_79, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.45  cnf(c_0_80, negated_conjecture, (k1_relat_1(k2_funct_1(esk7_0))!=k1_xboole_0|esk6_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))|~r1_tarski(k2_relat_1(k2_funct_1(esk7_0)),esk5_0)|~v1_xboole_0(esk7_0)), inference(pm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.45  cnf(c_0_81, plain, (k2_relat_1(k2_funct_1(X1))=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.45  cnf(c_0_82, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.45  cnf(c_0_83, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_84, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_85, negated_conjecture, (v1_relat_1(esk7_0)), inference(pm,[status(thm)],[c_0_26, c_0_57])).
% 0.20/0.45  cnf(c_0_86, negated_conjecture, (k1_relat_1(k2_funct_1(esk7_0))!=k1_xboole_0|esk6_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_63]), c_0_83]), c_0_84]), c_0_85])])).
% 0.20/0.45  cnf(c_0_87, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.45  fof(c_0_88, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.45  cnf(c_0_89, negated_conjecture, (k1_relat_1(k2_funct_1(esk7_0))!=k1_xboole_0|esk6_0!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk7_0))|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_87]), c_0_84]), c_0_85])])).
% 0.20/0.45  fof(c_0_90, plain, ![X40, X41, X42]:((((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))))&((~v1_funct_2(X42,X40,X41)|X42=k1_xboole_0|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X42!=k1_xboole_0|v1_funct_2(X42,X40,X41)|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.45  cnf(c_0_91, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.20/0.45  cnf(c_0_92, negated_conjecture, (k1_relat_1(k2_funct_1(esk7_0))!=k1_xboole_0|esk6_0!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89, c_0_73]), c_0_84]), c_0_85])])).
% 0.20/0.45  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk6_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_57, c_0_24])).
% 0.20/0.45  cnf(c_0_94, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.20/0.45  cnf(c_0_95, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(pm,[status(thm)],[c_0_91, c_0_57])).
% 0.20/0.45  cnf(c_0_96, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_97, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92, c_0_78]), c_0_63]), c_0_83]), c_0_84]), c_0_85])])).
% 0.20/0.45  cnf(c_0_98, negated_conjecture, (v1_xboole_0(esk7_0)|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28, c_0_93]), c_0_30])])).
% 0.20/0.45  cnf(c_0_99, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_72, c_0_78])).
% 0.20/0.45  cnf(c_0_100, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94, c_0_57]), c_0_95]), c_0_96])])).
% 0.20/0.45  cnf(c_0_101, negated_conjecture, (esk6_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.45  cnf(c_0_102, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.45  cnf(c_0_103, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_relat_1(k2_funct_1(esk7_0)))))|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99, c_0_63]), c_0_83]), c_0_84]), c_0_85])])).
% 0.20/0.45  cnf(c_0_104, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.45  cnf(c_0_105, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(sr,[status(thm)],[c_0_100, c_0_101])).
% 0.20/0.45  cnf(c_0_106, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_102, c_0_78])).
% 0.20/0.45  cnf(c_0_107, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_83]), c_0_84]), c_0_85])])).
% 0.20/0.45  cnf(c_0_108, negated_conjecture, (v1_funct_2(k2_funct_1(esk7_0),esk6_0,k2_relat_1(k2_funct_1(esk7_0)))|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106, c_0_63]), c_0_83]), c_0_84]), c_0_85])])).
% 0.20/0.45  cnf(c_0_109, negated_conjecture, (~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(pm,[status(thm)],[c_0_61, c_0_107])).
% 0.20/0.45  cnf(c_0_110, negated_conjecture, (v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_108, c_0_104]), c_0_83]), c_0_84]), c_0_85])]), c_0_105])).
% 0.20/0.45  cnf(c_0_111, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))|~v1_relat_1(k2_funct_1(esk7_0))), inference(pm,[status(thm)],[c_0_109, c_0_110])).
% 0.20/0.45  cnf(c_0_112, negated_conjecture, (~v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111, c_0_87]), c_0_84]), c_0_85])])).
% 0.20/0.45  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_112, c_0_73]), c_0_84]), c_0_85])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 114
% 0.20/0.45  # Proof object clause steps            : 77
% 0.20/0.45  # Proof object formula steps           : 37
% 0.20/0.45  # Proof object conjectures             : 34
% 0.20/0.45  # Proof object clause conjectures      : 31
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 31
% 0.20/0.45  # Proof object initial formulas used   : 19
% 0.20/0.45  # Proof object generating inferences   : 45
% 0.20/0.45  # Proof object simplifying inferences  : 53
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 20
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 47
% 0.20/0.45  # Removed in clause preprocessing      : 2
% 0.20/0.45  # Initial clauses in saturation        : 45
% 0.20/0.45  # Processed clauses                    : 825
% 0.20/0.45  # ...of these trivial                  : 8
% 0.20/0.45  # ...subsumed                          : 436
% 0.20/0.45  # ...remaining for further processing  : 381
% 0.20/0.45  # Other redundant clauses eliminated   : 0
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 91
% 0.20/0.45  # Backward-rewritten                   : 47
% 0.20/0.45  # Generated clauses                    : 4133
% 0.20/0.45  # ...of the previous two non-trivial   : 3820
% 0.20/0.45  # Contextual simplify-reflections      : 0
% 0.20/0.45  # Paramodulations                      : 4100
% 0.20/0.45  # Factorizations                       : 4
% 0.20/0.45  # Equation resolutions                 : 28
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 242
% 0.20/0.45  #    Positive orientable unit clauses  : 27
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 8
% 0.20/0.45  #    Non-unit-clauses                  : 207
% 0.20/0.45  # Current number of unprocessed clauses: 2930
% 0.20/0.45  # ...number of literals in the above   : 14536
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 139
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 3666
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 2328
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 398
% 0.20/0.45  # Unit Clause-clause subsumption calls : 310
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 15
% 0.20/0.45  # BW rewrite match successes           : 9
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 30314
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.105 s
% 0.20/0.45  # System time              : 0.005 s
% 0.20/0.45  # Total time               : 0.109 s
% 0.20/0.45  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
