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
% DateTime   : Thu Dec  3 11:07:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 341 expanded)
%              Number of clauses        :   56 ( 135 expanded)
%              Number of leaves         :   15 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  300 (1863 expanded)
%              Number of equality atoms :   79 ( 412 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t186_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t185_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t7_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(d8_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => k7_partfun1(X1,X2,X3) = k1_funct_1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(c_0_15,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_16,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk2_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk3_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ! [X5] :
                ( ( v1_funct_1(X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                     => ( X2 = k1_xboole_0
                        | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_funct_2])).

cnf(c_0_20,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    & v1_funct_1(esk9_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))
    & m1_subset_1(esk10_0,esk6_0)
    & r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))
    & esk6_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) != k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_23,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_24,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_20])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ~ m1_subset_1(X11,X12)
      | v1_xboole_0(X12)
      | r2_hidden(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_24])).

cnf(c_0_32,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_33,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( v1_xboole_0(X47)
      | ~ v1_funct_1(X48)
      | ~ v1_funct_2(X48,X46,X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))
      | ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))
      | ~ m1_subset_1(X50,X46)
      | ~ r1_tarski(k2_relset_1(X46,X47,X48),k1_relset_1(X47,X45,X49))
      | X46 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X46,X47,X45,X48,X49),X50) = k1_funct_1(X49,k1_funct_1(X48,X50)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_34,plain,(
    ! [X51,X52] :
      ( ( v1_funct_1(X52)
        | ~ r1_tarski(k2_relat_1(X52),X51)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,k1_relat_1(X52),X51)
        | ~ r1_tarski(k2_relat_1(X52),X51)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X52),X51)))
        | ~ r1_tarski(k2_relat_1(X52),X51)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k1_relset_1(esk7_0,esk5_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(esk6_0,esk7_0,esk8_0) = k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk10_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_43,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X41 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X41 != k1_xboole_0
        | v1_funct_2(X41,X39,X40)
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k1_funct_1(X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_47,plain,(
    ! [X27,X28,X29] :
      ( ( v4_relat_1(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( v5_relat_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_48,plain,(
    ! [X53,X54,X55,X56] :
      ( ~ v1_funct_1(X56)
      | ~ v1_funct_2(X56,X53,X54)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))
      | ~ r2_hidden(X55,X53)
      | X54 = k1_xboole_0
      | r2_hidden(k1_funct_1(X56,X55),X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).

cnf(c_0_49,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0)
    | v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42])]),c_0_32])])).

cnf(c_0_56,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3) = k1_funct_1(esk9_0,k1_funct_1(X2,X3))
    | X1 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relat_1(esk9_0))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))
    | ~ m1_subset_1(X3,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_45]),c_0_26])]),c_0_46])).

fof(c_0_60,plain,(
    ! [X42,X43,X44] :
      ( ~ v1_relat_1(X43)
      | ~ v5_relat_1(X43,X42)
      | ~ v1_funct_1(X43)
      | ~ r2_hidden(X44,k1_relat_1(X43))
      | k7_partfun1(X42,X43,X44) = k1_funct_1(X43,X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).

cnf(c_0_61,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(esk8_0,k1_relat_1(esk8_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),k1_relat_1(esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk10_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_relat_1(esk8_0)
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_28])])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_37]),c_0_50]),c_0_51]),c_0_57]),c_0_28])]),c_0_41])).

fof(c_0_68,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_xboole_0(X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_69,plain,
    ( k7_partfun1(X2,X1,X3) = k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( v5_relat_1(esk9_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,X1),k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_51])]),c_0_64])])).

cnf(c_0_73,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk10_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) != k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0) = k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_40])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k7_partfun1(esk5_0,esk9_0,X1) = k1_funct_1(esk9_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_45]),c_0_71])])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk8_0,esk10_0),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)) != k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | k1_relat_1(esk8_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_24])]),c_0_32])])).

cnf(c_0_84,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_32])]),c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_84]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.51  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.51  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.51  #
% 0.20/0.51  # Preprocessing time       : 0.029 s
% 0.20/0.51  # Presaturation interreduction done
% 0.20/0.51  
% 0.20/0.51  # Proof found!
% 0.20/0.51  # SZS status Theorem
% 0.20/0.51  # SZS output start CNFRefutation
% 0.20/0.51  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.51  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.51  fof(t186_funct_2, conjecture, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 0.20/0.51  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.51  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.51  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.51  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.51  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.51  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.20/0.51  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.51  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.51  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.51  fof(t7_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 0.20/0.51  fof(d8_partfun1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>k7_partfun1(X1,X2,X3)=k1_funct_1(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 0.20/0.51  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.51  fof(c_0_15, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.51  fof(c_0_16, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:(((~r2_hidden(X15,X14)|r2_hidden(k4_tarski(X15,esk2_3(X13,X14,X15)),X13)|X14!=k1_relat_1(X13))&(~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(X17,X14)|X14!=k1_relat_1(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|~r2_hidden(k4_tarski(esk3_2(X19,X20),X22),X19)|X20=k1_relat_1(X19))&(r2_hidden(esk3_2(X19,X20),X20)|r2_hidden(k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)),X19)|X20=k1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.51  cnf(c_0_17, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.51  cnf(c_0_18, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.51  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k7_partfun1(X1,X5,k1_funct_1(X4,X6))))))))), inference(assume_negation,[status(cth)],[t186_funct_2])).
% 0.20/0.51  cnf(c_0_20, plain, (X1=k1_relat_1(X2)|r2_hidden(esk3_2(X2,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.51  fof(c_0_21, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.51  fof(c_0_22, negated_conjecture, (~v1_xboole_0(esk7_0)&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((v1_funct_1(esk9_0)&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0))))&(m1_subset_1(esk10_0,esk6_0)&(r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))&(esk6_0!=k1_xboole_0&k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)!=k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.20/0.51  fof(c_0_23, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k2_relset_1(X36,X37,X38)=k2_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.51  cnf(c_0_24, plain, (X1=k1_relat_1(X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_17, c_0_20])).
% 0.20/0.51  cnf(c_0_25, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.51  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.51  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  fof(c_0_29, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.51  fof(c_0_30, plain, ![X11, X12]:(~m1_subset_1(X11,X12)|(v1_xboole_0(X12)|r2_hidden(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.51  cnf(c_0_31, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_24, c_0_24])).
% 0.20/0.51  cnf(c_0_32, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.51  fof(c_0_33, plain, ![X45, X46, X47, X48, X49, X50]:(v1_xboole_0(X47)|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))|(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))|(~m1_subset_1(X50,X46)|(~r1_tarski(k2_relset_1(X46,X47,X48),k1_relset_1(X47,X45,X49))|(X46=k1_xboole_0|k1_funct_1(k8_funct_2(X46,X47,X45,X48,X49),X50)=k1_funct_1(X49,k1_funct_1(X48,X50)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.20/0.51  fof(c_0_34, plain, ![X51, X52]:(((v1_funct_1(X52)|~r1_tarski(k2_relat_1(X52),X51)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(v1_funct_2(X52,k1_relat_1(X52),X51)|~r1_tarski(k2_relat_1(X52),X51)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X52),X51)))|~r1_tarski(k2_relat_1(X52),X51)|(~v1_relat_1(X52)|~v1_funct_1(X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.51  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_relset_1(esk6_0,esk7_0,esk8_0),k1_relset_1(esk7_0,esk5_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_36, negated_conjecture, (k1_relset_1(esk7_0,esk5_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.51  cnf(c_0_37, negated_conjecture, (k2_relset_1(esk6_0,esk7_0,esk8_0)=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.51  cnf(c_0_38, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.51  cnf(c_0_39, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.51  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk10_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_41, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_42, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.51  fof(c_0_43, plain, ![X39, X40, X41]:((((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&((~v1_funct_2(X41,X39,X40)|X41=k1_xboole_0|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X41!=k1_xboole_0|v1_funct_2(X41,X39,X40)|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.51  cnf(c_0_44, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.51  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  fof(c_0_47, plain, ![X27, X28, X29]:((v4_relat_1(X29,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(v5_relat_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.51  fof(c_0_48, plain, ![X53, X54, X55, X56]:(~v1_funct_1(X56)|~v1_funct_2(X56,X53,X54)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))|(~r2_hidden(X55,X53)|(X54=k1_xboole_0|r2_hidden(k1_funct_1(X56,X55),X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_funct_2])])).
% 0.20/0.51  cnf(c_0_49, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.51  cnf(c_0_50, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),k1_relat_1(esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.20/0.51  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_28])).
% 0.20/0.51  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.51  cnf(c_0_54, negated_conjecture, (r2_hidden(esk10_0,esk6_0)|v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.51  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42])]), c_0_32])])).
% 0.20/0.51  cnf(c_0_56, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.51  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_58, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_28])).
% 0.20/0.51  cnf(c_0_59, negated_conjecture, (k1_funct_1(k8_funct_2(X1,esk7_0,esk5_0,X2,esk9_0),X3)=k1_funct_1(esk9_0,k1_funct_1(X2,X3))|X1=k1_xboole_0|~r1_tarski(k2_relset_1(X1,esk7_0,X2),k1_relat_1(esk9_0))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk7_0)))|~m1_subset_1(X3,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_45]), c_0_26])]), c_0_46])).
% 0.20/0.51  fof(c_0_60, plain, ![X42, X43, X44]:(~v1_relat_1(X43)|~v5_relat_1(X43,X42)|~v1_funct_1(X43)|(~r2_hidden(X44,k1_relat_1(X43))|k7_partfun1(X42,X43,X44)=k1_funct_1(X43,X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_partfun1])])])).
% 0.20/0.51  cnf(c_0_61, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.51  cnf(c_0_62, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.51  cnf(c_0_63, negated_conjecture, (v1_funct_2(esk8_0,k1_relat_1(esk8_0),k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])])).
% 0.20/0.51  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),k1_relat_1(esk9_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_50]), c_0_51]), c_0_52])])).
% 0.20/0.51  cnf(c_0_65, negated_conjecture, (r2_hidden(esk10_0,esk6_0)), inference(sr,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.51  cnf(c_0_66, negated_conjecture, (esk6_0=k1_relat_1(esk8_0)|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58]), c_0_28])])).
% 0.20/0.51  cnf(c_0_67, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),X1)=k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1))|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_37]), c_0_50]), c_0_51]), c_0_57]), c_0_28])]), c_0_41])).
% 0.20/0.51  fof(c_0_68, plain, ![X30, X31, X32]:(~v1_xboole_0(X30)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.51  cnf(c_0_69, plain, (k7_partfun1(X2,X1,X3)=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.51  cnf(c_0_70, negated_conjecture, (v5_relat_1(esk9_0,esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_26])).
% 0.20/0.51  cnf(c_0_71, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_38, c_0_26])).
% 0.20/0.51  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,X1),k1_relat_1(esk9_0))|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_51])]), c_0_64])])).
% 0.20/0.51  cnf(c_0_73, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk10_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.51  cnf(c_0_74, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)!=k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.51  cnf(c_0_75, negated_conjecture, (k1_funct_1(k8_funct_2(esk6_0,esk7_0,esk5_0,esk8_0,esk9_0),esk10_0)=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(spm,[status(thm)],[c_0_67, c_0_40])).
% 0.20/0.51  cnf(c_0_76, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.51  cnf(c_0_77, negated_conjecture, (k7_partfun1(esk5_0,esk9_0,X1)=k1_funct_1(esk9_0,X1)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_45]), c_0_71])])).
% 0.20/0.51  cnf(c_0_78, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|esk7_0=k1_xboole_0|r2_hidden(k1_funct_1(esk8_0,esk10_0),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.51  cnf(c_0_79, negated_conjecture, (k7_partfun1(esk5_0,esk9_0,k1_funct_1(esk8_0,esk10_0))!=k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk10_0))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.51  cnf(c_0_80, negated_conjecture, (esk7_0=k1_xboole_0|k1_relat_1(esk8_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_66])).
% 0.20/0.51  cnf(c_0_81, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_76, c_0_64])).
% 0.20/0.51  cnf(c_0_82, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.20/0.51  cnf(c_0_83, negated_conjecture, (esk7_0=k1_xboole_0|~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_24])]), c_0_32])])).
% 0.20/0.51  cnf(c_0_84, negated_conjecture, (esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_32])]), c_0_83])).
% 0.20/0.51  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_84]), c_0_32])]), ['proof']).
% 0.20/0.51  # SZS output end CNFRefutation
% 0.20/0.51  # Proof object total steps             : 86
% 0.20/0.51  # Proof object clause steps            : 56
% 0.20/0.51  # Proof object formula steps           : 30
% 0.20/0.51  # Proof object conjectures             : 40
% 0.20/0.51  # Proof object clause conjectures      : 37
% 0.20/0.51  # Proof object formula conjectures     : 3
% 0.20/0.51  # Proof object initial clauses used    : 25
% 0.20/0.51  # Proof object initial formulas used   : 15
% 0.20/0.51  # Proof object generating inferences   : 27
% 0.20/0.51  # Proof object simplifying inferences  : 43
% 0.20/0.51  # Training examples: 0 positive, 0 negative
% 0.20/0.51  # Parsed axioms                        : 15
% 0.20/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.51  # Initial clauses                      : 36
% 0.20/0.51  # Removed in clause preprocessing      : 1
% 0.20/0.51  # Initial clauses in saturation        : 35
% 0.20/0.51  # Processed clauses                    : 1494
% 0.20/0.51  # ...of these trivial                  : 1
% 0.20/0.51  # ...subsumed                          : 984
% 0.20/0.51  # ...remaining for further processing  : 509
% 0.20/0.51  # Other redundant clauses eliminated   : 202
% 0.20/0.51  # Clauses deleted for lack of memory   : 0
% 0.20/0.51  # Backward-subsumed                    : 13
% 0.20/0.51  # Backward-rewritten                   : 192
% 0.20/0.51  # Generated clauses                    : 4999
% 0.20/0.51  # ...of the previous two non-trivial   : 4889
% 0.20/0.51  # Contextual simplify-reflections      : 5
% 0.20/0.51  # Paramodulations                      : 4795
% 0.20/0.51  # Factorizations                       : 2
% 0.20/0.51  # Equation resolutions                 : 202
% 0.20/0.51  # Propositional unsat checks           : 0
% 0.20/0.51  #    Propositional check models        : 0
% 0.20/0.51  #    Propositional check unsatisfiable : 0
% 0.20/0.51  #    Propositional clauses             : 0
% 0.20/0.51  #    Propositional clauses after purity: 0
% 0.20/0.51  #    Propositional unsat core size     : 0
% 0.20/0.51  #    Propositional preprocessing time  : 0.000
% 0.20/0.51  #    Propositional encoding time       : 0.000
% 0.20/0.51  #    Propositional solver time         : 0.000
% 0.20/0.51  #    Success case prop preproc time    : 0.000
% 0.20/0.51  #    Success case prop encoding time   : 0.000
% 0.20/0.51  #    Success case prop solver time     : 0.000
% 0.20/0.51  # Current number of processed clauses  : 262
% 0.20/0.51  #    Positive orientable unit clauses  : 17
% 0.20/0.51  #    Positive unorientable unit clauses: 0
% 0.20/0.51  #    Negative unit clauses             : 3
% 0.20/0.51  #    Non-unit-clauses                  : 242
% 0.20/0.51  # Current number of unprocessed clauses: 3078
% 0.20/0.51  # ...number of literals in the above   : 16680
% 0.20/0.51  # Current number of archived formulas  : 0
% 0.20/0.51  # Current number of archived clauses   : 241
% 0.20/0.51  # Clause-clause subsumption calls (NU) : 64950
% 0.20/0.51  # Rec. Clause-clause subsumption calls : 15438
% 0.20/0.51  # Non-unit clause-clause subsumptions  : 864
% 0.20/0.51  # Unit Clause-clause subsumption calls : 152
% 0.20/0.51  # Rewrite failures with RHS unbound    : 0
% 0.20/0.51  # BW rewrite match attempts            : 16
% 0.20/0.51  # BW rewrite match successes           : 4
% 0.20/0.51  # Condensation attempts                : 0
% 0.20/0.51  # Condensation successes               : 0
% 0.20/0.51  # Termbank termtop insertions          : 83829
% 0.20/0.51  
% 0.20/0.51  # -------------------------------------------------
% 0.20/0.51  # User time                : 0.152 s
% 0.20/0.51  # System time              : 0.010 s
% 0.20/0.51  # Total time               : 0.162 s
% 0.20/0.51  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
