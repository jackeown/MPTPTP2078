%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:58:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 190 expanded)
%              Number of clauses        :   43 (  79 expanded)
%              Number of leaves         :   16 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  214 ( 616 expanded)
%              Number of equality atoms :   45 ( 107 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_relset_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
             => ~ ( k1_relset_1(X1,X2,X3) != k1_xboole_0
                  & ! [X4] :
                      ( m1_subset_1(X4,X2)
                     => ~ r2_hidden(X4,k2_relset_1(X1,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
               => ~ ( k1_relset_1(X1,X2,X3) != k1_xboole_0
                    & ! [X4] :
                        ( m1_subset_1(X4,X2)
                       => ~ r2_hidden(X4,k2_relset_1(X1,X2,X3)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_relset_1])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X17] :
      ( X17 = k1_xboole_0
      | r2_hidden(esk3_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_19,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k1_relset_1(X40,X41,X42) = k1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_20,negated_conjecture,(
    ! [X49] :
      ( ~ v1_xboole_0(esk4_0)
      & ~ v1_xboole_0(esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & k1_relset_1(esk4_0,esk5_0,esk6_0) != k1_xboole_0
      & ( ~ m1_subset_1(X49,esk5_0)
        | ~ r2_hidden(X49,k2_relset_1(esk4_0,esk5_0,esk6_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X28,X29] :
      ( ( ~ v5_relat_1(X29,X28)
        | r1_tarski(k2_relat_1(X29),X28)
        | ~ v1_relat_1(X29) )
      & ( ~ r1_tarski(k2_relat_1(X29),X28)
        | v5_relat_1(X29,X28)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_24,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_25,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | v1_relat_1(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_26,plain,(
    ! [X30,X31] : v1_relat_1(k2_zfmisc_1(X30,X31)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_27,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ( k7_relat_1(X36,X35) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X36),X35)
        | ~ v1_relat_1(X36) )
      & ( ~ r1_xboole_0(k1_relat_1(X36),X35)
        | k7_relat_1(X36,X35) = k1_xboole_0
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

fof(c_0_29,plain,(
    ! [X26,X27] :
      ( ( ~ v4_relat_1(X27,X26)
        | r1_tarski(k1_relat_1(X27),X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_tarski(k1_relat_1(X27),X26)
        | v4_relat_1(X27,X26)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_33,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_39,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k2_relset_1(X43,X44,X45) = k2_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk3_1(k2_relat_1(X1)),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_38])])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(X1,esk5_0)
    | ~ r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_52,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk3_1(k1_relat_1(X1)),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk6_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | r2_hidden(esk3_1(k2_relat_1(esk6_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k1_xboole_0
    | ~ m1_subset_1(esk3_1(k2_relset_1(esk4_0,esk5_0,esk6_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_31])).

cnf(c_0_63,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk3_1(k1_relat_1(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_1(k1_relat_1(esk6_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_50])]),c_0_56])).

fof(c_0_65,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v4_relat_1(X33,X32)
      | X33 = k7_relat_1(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

fof(c_0_66,plain,(
    ! [X34] :
      ( ( k1_relat_1(X34) != k1_xboole_0
        | X34 = k1_xboole_0
        | ~ v1_relat_1(X34) )
      & ( k2_relat_1(X34) != k1_xboole_0
        | X34 = k1_xboole_0
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_67,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | m1_subset_1(esk3_1(k2_relat_1(esk6_0)),X1)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | ~ m1_subset_1(esk3_1(k2_relat_1(esk6_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( k7_relat_1(esk6_0,esk4_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_50])]),c_0_56])).

cnf(c_0_71,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_55]),c_0_50])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_50])]),c_0_74]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:31:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.042 s
% 0.20/0.43  # Presaturation interreduction done
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t49_relset_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.20/0.43  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.43  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.43  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.43  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.43  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.43  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.20/0.43  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.43  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.43  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.43  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.20/0.43  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.43  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~((k1_relset_1(X1,X2,X3)!=k1_xboole_0&![X4]:(m1_subset_1(X4,X2)=>~(r2_hidden(X4,k2_relset_1(X1,X2,X3)))))))))), inference(assume_negation,[status(cth)],[t49_relset_1])).
% 0.20/0.43  fof(c_0_17, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  fof(c_0_18, plain, ![X17]:(X17=k1_xboole_0|r2_hidden(esk3_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.20/0.43  fof(c_0_19, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k1_relset_1(X40,X41,X42)=k1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.43  fof(c_0_20, negated_conjecture, ![X49]:(~v1_xboole_0(esk4_0)&(~v1_xboole_0(esk5_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))&(k1_relset_1(esk4_0,esk5_0,esk6_0)!=k1_xboole_0&(~m1_subset_1(X49,esk5_0)|~r2_hidden(X49,k2_relset_1(esk4_0,esk5_0,esk6_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).
% 0.20/0.43  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_22, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  fof(c_0_23, plain, ![X28, X29]:((~v5_relat_1(X29,X28)|r1_tarski(k2_relat_1(X29),X28)|~v1_relat_1(X29))&(~r1_tarski(k2_relat_1(X29),X28)|v5_relat_1(X29,X28)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.43  fof(c_0_24, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.43  fof(c_0_25, plain, ![X24, X25]:(~v1_relat_1(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|v1_relat_1(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.43  fof(c_0_26, plain, ![X30, X31]:v1_relat_1(k2_zfmisc_1(X30,X31)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.43  fof(c_0_27, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.43  fof(c_0_28, plain, ![X35, X36]:((k7_relat_1(X36,X35)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X36),X35)|~v1_relat_1(X36))&(~r1_xboole_0(k1_relat_1(X36),X35)|k7_relat_1(X36,X35)=k1_xboole_0|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.20/0.43  fof(c_0_29, plain, ![X26, X27]:((~v4_relat_1(X27,X26)|r1_tarski(k1_relat_1(X27),X26)|~v1_relat_1(X27))&(~r1_tarski(k1_relat_1(X27),X26)|v4_relat_1(X27,X26)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.43  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  fof(c_0_32, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.43  fof(c_0_33, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.43  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.43  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.43  cnf(c_0_36, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_37, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.43  cnf(c_0_38, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.43  fof(c_0_39, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k2_relset_1(X43,X44,X45)=k2_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.43  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.43  cnf(c_0_41, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.43  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.43  cnf(c_0_43, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.43  cnf(c_0_44, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.43  cnf(c_0_46, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.43  cnf(c_0_47, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.43  cnf(c_0_48, plain, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk3_1(k2_relat_1(X1)),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.43  cnf(c_0_49, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 0.20/0.43  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_38])])).
% 0.20/0.43  cnf(c_0_51, negated_conjecture, (~m1_subset_1(X1,esk5_0)|~r2_hidden(X1,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_52, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_53, plain, (k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.43  cnf(c_0_54, plain, (k1_relat_1(X1)=k1_xboole_0|r2_hidden(esk3_1(k1_relat_1(X1)),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_42])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_31])).
% 0.20/0.43  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk6_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.43  cnf(c_0_57, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|r2_hidden(esk3_1(k2_relat_1(esk6_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.43  cnf(c_0_59, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_60, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_61, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k1_xboole_0|~m1_subset_1(esk3_1(k2_relset_1(esk4_0,esk5_0,esk6_0)),esk5_0)), inference(spm,[status(thm)],[c_0_51, c_0_22])).
% 0.20/0.43  cnf(c_0_62, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_31])).
% 0.20/0.43  cnf(c_0_63, plain, (k1_relat_1(X1)=k1_xboole_0|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(esk3_1(k1_relat_1(X1)),X2)), inference(spm,[status(thm)],[c_0_53, c_0_22])).
% 0.20/0.43  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_1(k1_relat_1(esk6_0)),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_50])]), c_0_56])).
% 0.20/0.43  fof(c_0_65, plain, ![X32, X33]:(~v1_relat_1(X33)|~v4_relat_1(X33,X32)|X33=k7_relat_1(X33,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.20/0.43  fof(c_0_66, plain, ![X34]:((k1_relat_1(X34)!=k1_xboole_0|X34=k1_xboole_0|~v1_relat_1(X34))&(k2_relat_1(X34)!=k1_xboole_0|X34=k1_xboole_0|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|m1_subset_1(esk3_1(k2_relat_1(esk6_0)),X1)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.43  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.43  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|~m1_subset_1(esk3_1(k2_relat_1(esk6_0)),esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (k7_relat_1(esk6_0,esk4_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_50])]), c_0_56])).
% 0.20/0.43  cnf(c_0_71, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.43  cnf(c_0_72, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_55]), c_0_50])])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_50])]), c_0_74]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 76
% 0.20/0.43  # Proof object clause steps            : 43
% 0.20/0.43  # Proof object formula steps           : 33
% 0.20/0.43  # Proof object conjectures             : 21
% 0.20/0.43  # Proof object clause conjectures      : 18
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 21
% 0.20/0.43  # Proof object initial formulas used   : 16
% 0.20/0.43  # Proof object generating inferences   : 20
% 0.20/0.43  # Proof object simplifying inferences  : 20
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 16
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 30
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 30
% 0.20/0.43  # Processed clauses                    : 499
% 0.20/0.43  # ...of these trivial                  : 0
% 0.20/0.43  # ...subsumed                          : 229
% 0.20/0.43  # ...remaining for further processing  : 270
% 0.20/0.43  # Other redundant clauses eliminated   : 7
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 17
% 0.20/0.43  # Backward-rewritten                   : 19
% 0.20/0.43  # Generated clauses                    : 783
% 0.20/0.43  # ...of the previous two non-trivial   : 745
% 0.20/0.43  # Contextual simplify-reflections      : 18
% 0.20/0.43  # Paramodulations                      : 774
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 7
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 202
% 0.20/0.43  #    Positive orientable unit clauses  : 14
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 5
% 0.20/0.43  #    Non-unit-clauses                  : 183
% 0.20/0.43  # Current number of unprocessed clauses: 293
% 0.20/0.43  # ...number of literals in the above   : 1062
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 68
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 6038
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 4591
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 263
% 0.20/0.43  # Unit Clause-clause subsumption calls : 92
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 7
% 0.20/0.43  # BW rewrite match successes           : 3
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 12912
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.082 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.088 s
% 0.20/0.43  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
