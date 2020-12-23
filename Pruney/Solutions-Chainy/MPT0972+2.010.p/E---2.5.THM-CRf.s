%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:43 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 (1217 expanded)
%              Number of clauses        :   67 ( 491 expanded)
%              Number of leaves         :   15 ( 297 expanded)
%              Depth                    :   19
%              Number of atoms          :  304 (6278 expanded)
%              Number of equality atoms :   88 (1343 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t6_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
     => ~ ( r2_hidden(X1,X4)
          & ! [X5,X6] :
              ~ ( X1 = k4_tarski(X5,X6)
                & r2_hidden(X5,X2)
                & r2_hidden(X6,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( r2_hidden(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_2])).

fof(c_0_16,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k1_relset_1(X39,X40,X41) = k1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_17,negated_conjecture,(
    ! [X59] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & ( ~ r2_hidden(X59,esk6_0)
        | k1_funct_1(esk8_0,X59) = k1_funct_1(esk9_0,X59) )
      & ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X52,X53,X54] :
      ( ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X53 = k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X52 = k1_relset_1(X52,X53,X54)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X52 != k1_relset_1(X52,X53,X54)
        | v1_funct_2(X54,X52,X53)
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( ~ v1_funct_2(X54,X52,X53)
        | X54 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != k1_xboole_0
        | v1_funct_2(X54,X52,X53)
        | X52 = k1_xboole_0
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_19,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | v1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X28,X29] :
      ( ( r2_hidden(esk3_2(X28,X29),k1_relat_1(X28))
        | k1_relat_1(X28) != k1_relat_1(X29)
        | X28 = X29
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( k1_funct_1(X28,esk3_2(X28,X29)) != k1_funct_1(X29,esk3_2(X28,X29))
        | k1_relat_1(X28) != k1_relat_1(X29)
        | X28 = X29
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_23,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24]),c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_34,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_35,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_36,plain,(
    ! [X46,X47,X48,X49] :
      ( ( X46 = k4_tarski(esk4_4(X46,X47,X48,X49),esk5_4(X46,X47,X48,X49))
        | ~ r2_hidden(X46,X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( r2_hidden(esk4_4(X46,X47,X48,X49),X47)
        | ~ r2_hidden(X46,X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( r2_hidden(esk5_4(X46,X47,X48,X49),X48)
        | ~ r2_hidden(X46,X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).

cnf(c_0_37,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk8_0 = X1
    | r2_hidden(esk3_2(esk8_0,X1),esk6_0)
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_32]),c_0_33])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_41,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk3_2(X1,X2)) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = k1_funct_1(esk9_0,X1)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( esk8_0 = esk9_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_48,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_49,plain,(
    ! [X19] : r1_tarski(k1_xboole_0,X19) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_4(X1,esk6_0,esk7_0,esk9_0),esk7_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | X1 = esk9_0
    | k1_funct_1(X1,esk3_2(X1,esk9_0)) != k1_funct_1(esk9_0,esk3_2(X1,esk9_0))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk8_0,esk3_2(esk8_0,esk9_0)) = k1_funct_1(esk9_0,esk3_2(esk8_0,esk9_0))
    | esk7_0 = k1_xboole_0
    | esk8_0 = esk9_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_58,plain,(
    ! [X42,X43,X44,X45] :
      ( ( ~ r2_relset_1(X42,X43,X44,X45)
        | X44 = X45
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != X45
        | r2_relset_1(X42,X43,X44,X45)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_59,plain,(
    ! [X36,X37,X38] :
      ( ( v4_relat_1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v5_relat_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_60,plain,(
    ! [X22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk5_4(esk1_1(esk9_0),esk6_0,esk7_0,esk9_0),esk7_0)
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( esk8_0 = esk9_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_29]),c_0_30]),c_0_31])]),c_0_55])).

cnf(c_0_64,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X26,X27] :
      ( ( ~ v4_relat_1(X27,X26)
        | r1_tarski(k1_relat_1(X27),X26)
        | ~ v1_relat_1(X27) )
      & ( ~ r1_tarski(k1_relat_1(X27),X26)
        | v4_relat_1(X27,X26)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_67,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( esk8_0 = esk9_0
    | v1_xboole_0(esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_71,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( esk8_0 = esk9_0
    | esk9_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r2_relset_1(esk6_0,esk7_0,esk9_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_27])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_57])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk5_4(X1,esk6_0,esk7_0,esk8_0),esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_20])).

cnf(c_0_81,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])])).

cnf(c_0_82,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk5_4(esk1_1(esk8_0),esk6_0,esk7_0,esk8_0),esk7_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_53])).

cnf(c_0_85,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_81]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk4_4(X1,esk6_0,esk7_0,esk8_0),esk6_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_20])).

cnf(c_0_87,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_xboole_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_64])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk4_4(esk1_1(esk8_0),esk6_0,esk7_0,esk8_0),esk6_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_53])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,esk8_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_75,c_0_81])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_87])).

cnf(c_0_91,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_68])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])])).

cnf(c_0_94,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_53])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93]),c_0_94])])).

cnf(c_0_96,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_93]),c_0_96]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:59:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.19/0.40  # and selection function SelectNewComplexAHP.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t18_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 0.19/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.40  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.40  fof(t6_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))=>~((r2_hidden(X1,X4)&![X5, X6]:~(((X1=k4_tarski(X5,X6)&r2_hidden(X5,X2))&r2_hidden(X6,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.40  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.40  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t18_funct_2])).
% 0.19/0.40  fof(c_0_16, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k1_relset_1(X39,X40,X41)=k1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.40  fof(c_0_17, negated_conjecture, ![X59]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((~r2_hidden(X59,esk6_0)|k1_funct_1(esk8_0,X59)=k1_funct_1(esk9_0,X59))&~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.19/0.40  fof(c_0_18, plain, ![X52, X53, X54]:((((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X53=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&((~v1_funct_2(X54,X52,X53)|X52=k1_relset_1(X52,X53,X54)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X52!=k1_relset_1(X52,X53,X54)|v1_funct_2(X54,X52,X53)|X52!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))))&((~v1_funct_2(X54,X52,X53)|X54=k1_xboole_0|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))&(X54!=k1_xboole_0|v1_funct_2(X54,X52,X53)|X52=k1_xboole_0|X53!=k1_xboole_0|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.40  cnf(c_0_19, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  fof(c_0_21, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.40  fof(c_0_22, plain, ![X28, X29]:((r2_hidden(esk3_2(X28,X29),k1_relat_1(X28))|k1_relat_1(X28)!=k1_relat_1(X29)|X28=X29|(~v1_relat_1(X29)|~v1_funct_1(X29))|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(k1_funct_1(X28,esk3_2(X28,X29))!=k1_funct_1(X29,esk3_2(X28,X29))|k1_relat_1(X28)!=k1_relat_1(X29)|X28=X29|(~v1_relat_1(X29)|~v1_funct_1(X29))|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.19/0.40  cnf(c_0_23, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_28, plain, (r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_24]), c_0_25])])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_20])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_19, c_0_27])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  fof(c_0_34, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.40  fof(c_0_35, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.40  fof(c_0_36, plain, ![X46, X47, X48, X49]:(((X46=k4_tarski(esk4_4(X46,X47,X48,X49),esk5_4(X46,X47,X48,X49))|~r2_hidden(X46,X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(r2_hidden(esk4_4(X46,X47,X48,X49),X47)|~r2_hidden(X46,X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&(r2_hidden(esk5_4(X46,X47,X48,X49),X48)|~r2_hidden(X46,X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_relset_1])])])])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, (esk7_0=k1_xboole_0|esk8_0=X1|r2_hidden(esk3_2(esk8_0,X1),esk6_0)|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.19/0.40  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_32]), c_0_33])])).
% 0.19/0.40  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  fof(c_0_41, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  cnf(c_0_42, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_43, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.40  cnf(c_0_44, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X3)|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  cnf(c_0_45, plain, (X1=X2|k1_funct_1(X1,esk3_2(X1,X2))!=k1_funct_1(X2,esk3_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk8_0,X1)=k1_funct_1(esk9_0,X1)|~r2_hidden(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (esk8_0=esk9_0|esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.40  fof(c_0_48, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.40  fof(c_0_49, plain, ![X19]:r1_tarski(k1_xboole_0,X19), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.40  cnf(c_0_50, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.40  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.40  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_4(X1,esk6_0,esk7_0,esk9_0),esk7_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_44, c_0_27])).
% 0.19/0.40  cnf(c_0_53, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (esk7_0=k1_xboole_0|X1=esk9_0|k1_funct_1(X1,esk3_2(X1,esk9_0))!=k1_funct_1(esk9_0,esk3_2(X1,esk9_0))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_39]), c_0_40])])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (k1_funct_1(esk8_0,esk3_2(esk8_0,esk9_0))=k1_funct_1(esk9_0,esk3_2(esk8_0,esk9_0))|esk7_0=k1_xboole_0|esk8_0=esk9_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.40  cnf(c_0_56, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.40  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.40  fof(c_0_58, plain, ![X42, X43, X44, X45]:((~r2_relset_1(X42,X43,X44,X45)|X44=X45|(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&(X44!=X45|r2_relset_1(X42,X43,X44,X45)|(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.40  fof(c_0_59, plain, ![X36, X37, X38]:((v4_relat_1(X38,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v5_relat_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.40  fof(c_0_60, plain, ![X22]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X22)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.40  cnf(c_0_61, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (r2_hidden(esk5_4(esk1_1(esk9_0),esk6_0,esk7_0,esk9_0),esk7_0)|v1_xboole_0(esk9_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (esk8_0=esk9_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_29]), c_0_30]), c_0_31])]), c_0_55])).
% 0.19/0.40  cnf(c_0_64, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.40  cnf(c_0_65, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.40  fof(c_0_66, plain, ![X26, X27]:((~v4_relat_1(X27,X26)|r1_tarski(k1_relat_1(X27),X26)|~v1_relat_1(X27))&(~r1_tarski(k1_relat_1(X27),X26)|v4_relat_1(X27,X26)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.40  cnf(c_0_67, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.40  cnf(c_0_68, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.40  cnf(c_0_69, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_57])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (esk8_0=esk9_0|v1_xboole_0(esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.19/0.40  cnf(c_0_71, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_65])).
% 0.19/0.40  cnf(c_0_72, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.40  cnf(c_0_73, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.40  cnf(c_0_74, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_68])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (esk8_0=esk9_0|esk9_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (r2_relset_1(esk6_0,esk7_0,esk9_0,esk9_0)), inference(spm,[status(thm)],[c_0_71, c_0_27])).
% 0.19/0.40  cnf(c_0_78, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_57])).
% 0.19/0.40  cnf(c_0_79, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (r2_hidden(esk5_4(X1,esk6_0,esk7_0,esk8_0),esk7_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_20])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])])).
% 0.19/0.40  cnf(c_0_82, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.40  cnf(c_0_83, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X1,X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (r2_hidden(esk5_4(esk1_1(esk8_0),esk6_0,esk7_0,esk8_0),esk7_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_80, c_0_53])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_81]), c_0_82])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (r2_hidden(esk4_4(X1,esk6_0,esk7_0,esk8_0),esk6_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_83, c_0_20])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (esk6_0=k1_xboole_0|v1_xboole_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_64])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (r2_hidden(esk4_4(esk1_1(esk8_0),esk6_0,esk7_0,esk8_0),esk6_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_86, c_0_53])).
% 0.19/0.40  cnf(c_0_89, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,esk8_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_75, c_0_81])).
% 0.19/0.40  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_87])).
% 0.19/0.40  cnf(c_0_91, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_68])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_42, c_0_88])).
% 0.19/0.40  cnf(c_0_93, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])])).
% 0.19/0.40  cnf(c_0_94, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_53])).
% 0.19/0.40  cnf(c_0_95, negated_conjecture, (v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93]), c_0_94])])).
% 0.19/0.40  cnf(c_0_96, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_95])).
% 0.19/0.40  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_93]), c_0_96]), c_0_91])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 98
% 0.19/0.40  # Proof object clause steps            : 67
% 0.19/0.40  # Proof object formula steps           : 31
% 0.19/0.40  # Proof object conjectures             : 41
% 0.19/0.40  # Proof object clause conjectures      : 38
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 25
% 0.19/0.40  # Proof object initial formulas used   : 15
% 0.19/0.40  # Proof object generating inferences   : 37
% 0.19/0.40  # Proof object simplifying inferences  : 38
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 17
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 42
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 42
% 0.19/0.40  # Processed clauses                    : 446
% 0.19/0.40  # ...of these trivial                  : 4
% 0.19/0.40  # ...subsumed                          : 149
% 0.19/0.40  # ...remaining for further processing  : 292
% 0.19/0.40  # Other redundant clauses eliminated   : 5
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 12
% 0.19/0.40  # Backward-rewritten                   : 139
% 0.19/0.40  # Generated clauses                    : 730
% 0.19/0.40  # ...of the previous two non-trivial   : 725
% 0.19/0.40  # Contextual simplify-reflections      : 2
% 0.19/0.40  # Paramodulations                      : 715
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 15
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 97
% 0.19/0.40  #    Positive orientable unit clauses  : 17
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 78
% 0.19/0.40  # Current number of unprocessed clauses: 346
% 0.19/0.40  # ...number of literals in the above   : 1429
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 192
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 8066
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 3044
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 150
% 0.19/0.40  # Unit Clause-clause subsumption calls : 175
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 22
% 0.19/0.40  # BW rewrite match successes           : 7
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 13767
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.061 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.065 s
% 0.19/0.40  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
