%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:23 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 591 expanded)
%              Number of clauses        :   48 ( 232 expanded)
%              Number of leaves         :   13 ( 144 expanded)
%              Depth                    :   16
%              Number of atoms          :  236 (3167 expanded)
%              Number of equality atoms :   79 ( 698 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t113_funct_2])).

fof(c_0_14,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,negated_conjecture,(
    ! [X53] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & ( ~ m1_subset_1(X53,esk5_0)
        | k1_funct_1(esk7_0,X53) = k1_funct_1(esk8_0,X53) )
      & ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X46,X47,X48] :
      ( ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X47 = k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X46 = k1_relset_1(X46,X47,X48)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X46 != k1_relset_1(X46,X47,X48)
        | v1_funct_2(X48,X46,X47)
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( ~ v1_funct_2(X48,X46,X47)
        | X48 = k1_xboole_0
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( X48 != k1_xboole_0
        | v1_funct_2(X48,X46,X47)
        | X46 = k1_xboole_0
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ( r2_hidden(esk2_2(X22,X23),k1_relat_1(X22))
        | k1_relat_1(X22) != k1_relat_1(X23)
        | X22 = X23
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_funct_1(X22,esk2_2(X22,X23)) != k1_funct_1(X23,esk2_2(X22,X23))
        | k1_relat_1(X22) != k1_relat_1(X23)
        | X22 = X23
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_21,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_22]),c_0_23])])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_32,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = X1
    | r2_hidden(esk2_2(esk7_0,X1),esk5_0)
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_30]),c_0_31])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | ~ r1_tarski(X26,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_38,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( esk7_0 = esk8_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_44,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_xboole_0(X30)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))
      | v1_xboole_0(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_funct_1(esk8_0,X1)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = esk8_0
    | m1_subset_1(esk2_2(esk7_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_48,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(X12)
      | X12 = X13
      | ~ v1_xboole_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | X1 = esk8_0
    | k1_funct_1(X1,esk2_2(X1,esk8_0)) != k1_funct_1(esk8_0,esk2_2(X1,esk8_0))
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0)) = k1_funct_1(esk8_0,esk2_2(esk7_0,esk8_0))
    | esk7_0 = esk8_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_54,plain,(
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

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_25])).

cnf(c_0_58,negated_conjecture,
    ( esk7_0 = esk8_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_27]),c_0_28]),c_0_29])]),c_0_53])).

cnf(c_0_59,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 = esk8_0
    | v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_56])])).

cnf(c_0_62,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( esk7_0 = esk8_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r2_relset_1(esk5_0,esk6_0,esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

fof(c_0_67,plain,(
    ! [X16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_66])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk6_0,esk7_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_56])]),c_0_60])).

cnf(c_0_73,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72]),c_0_73])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.13/0.41  # and selection function SelectNewComplexAHP.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.028 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t113_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 0.13/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.41  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.13/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.13/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.41  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.13/0.41  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.13/0.41  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.13/0.41  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.41  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t113_funct_2])).
% 0.13/0.41  fof(c_0_14, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.41  fof(c_0_15, negated_conjecture, ![X53]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((~m1_subset_1(X53,esk5_0)|k1_funct_1(esk7_0,X53)=k1_funct_1(esk8_0,X53))&~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.13/0.41  fof(c_0_16, plain, ![X46, X47, X48]:((((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X47=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&((~v1_funct_2(X48,X46,X47)|X46=k1_relset_1(X46,X47,X48)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X46!=k1_relset_1(X46,X47,X48)|v1_funct_2(X48,X46,X47)|X46!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))))&((~v1_funct_2(X48,X46,X47)|X48=k1_xboole_0|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(X48!=k1_xboole_0|v1_funct_2(X48,X46,X47)|X46=k1_xboole_0|X47!=k1_xboole_0|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.41  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.41  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  fof(c_0_19, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.41  fof(c_0_20, plain, ![X22, X23]:((r2_hidden(esk2_2(X22,X23),k1_relat_1(X22))|k1_relat_1(X22)!=k1_relat_1(X23)|X22=X23|(~v1_relat_1(X23)|~v1_funct_1(X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k1_funct_1(X22,esk2_2(X22,X23))!=k1_funct_1(X23,esk2_2(X22,X23))|k1_relat_1(X22)!=k1_relat_1(X23)|X22=X23|(~v1_relat_1(X23)|~v1_funct_1(X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.13/0.41  cnf(c_0_21, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_22, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.41  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.41  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_22]), c_0_23])])).
% 0.13/0.41  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.13/0.41  cnf(c_0_30, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.13/0.41  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  fof(c_0_32, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.41  cnf(c_0_33, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=X1|r2_hidden(esk2_2(esk7_0,X1),esk5_0)|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.13/0.41  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_25]), c_0_30]), c_0_31])])).
% 0.13/0.41  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.41  fof(c_0_37, plain, ![X25, X26]:(~r2_hidden(X25,X26)|~r1_tarski(X26,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.13/0.41  fof(c_0_38, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.41  cnf(c_0_39, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.41  cnf(c_0_40, negated_conjecture, (esk7_0=esk8_0|esk6_0=k1_xboole_0|r2_hidden(esk2_2(esk7_0,esk8_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.41  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.41  cnf(c_0_42, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.41  fof(c_0_43, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.41  fof(c_0_44, plain, ![X30, X31, X32]:(~v1_xboole_0(X30)|(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X31,X30)))|v1_xboole_0(X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.13/0.41  cnf(c_0_45, plain, (X1=X2|k1_funct_1(X1,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.41  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_funct_1(esk8_0,X1)|~m1_subset_1(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_47, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=esk8_0|m1_subset_1(esk2_2(esk7_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.41  fof(c_0_48, plain, ![X12, X13]:(~v1_xboole_0(X12)|X12=X13|~v1_xboole_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.13/0.41  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.41  cnf(c_0_50, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.41  cnf(c_0_51, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.13/0.41  cnf(c_0_52, negated_conjecture, (esk6_0=k1_xboole_0|X1=esk8_0|k1_funct_1(X1,esk2_2(X1,esk8_0))!=k1_funct_1(esk8_0,esk2_2(X1,esk8_0))|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk7_0,esk2_2(esk7_0,esk8_0))=k1_funct_1(esk8_0,esk2_2(esk7_0,esk8_0))|esk7_0=esk8_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.41  fof(c_0_54, plain, ![X36, X37, X38, X39]:((~r2_relset_1(X36,X37,X38,X39)|X38=X39|(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(X38!=X39|r2_relset_1(X36,X37,X38,X39)|(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.13/0.41  cnf(c_0_55, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.13/0.41  cnf(c_0_56, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.41  cnf(c_0_57, negated_conjecture, (v1_xboole_0(esk8_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_25])).
% 0.13/0.41  cnf(c_0_58, negated_conjecture, (esk7_0=esk8_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_27]), c_0_28]), c_0_29])]), c_0_53])).
% 0.13/0.41  cnf(c_0_59, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.41  cnf(c_0_60, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, (esk7_0=esk8_0|v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_56])])).
% 0.13/0.41  cnf(c_0_62, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_59])).
% 0.13/0.41  cnf(c_0_63, negated_conjecture, (~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.41  cnf(c_0_64, negated_conjecture, (esk7_0=esk8_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.41  cnf(c_0_65, negated_conjecture, (r2_relset_1(esk5_0,esk6_0,esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_62, c_0_25])).
% 0.13/0.41  cnf(c_0_66, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.13/0.41  fof(c_0_67, plain, ![X16]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X16)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.41  cnf(c_0_68, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_18])).
% 0.13/0.41  cnf(c_0_69, negated_conjecture, (esk6_0=k1_xboole_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_66])).
% 0.13/0.41  cnf(c_0_70, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.41  cnf(c_0_71, negated_conjecture, (~r2_relset_1(esk5_0,esk6_0,esk7_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_63, c_0_66])).
% 0.13/0.41  cnf(c_0_72, negated_conjecture, (esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_56])]), c_0_60])).
% 0.13/0.41  cnf(c_0_73, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_70])).
% 0.13/0.41  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72]), c_0_73])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 75
% 0.13/0.41  # Proof object clause steps            : 48
% 0.13/0.41  # Proof object formula steps           : 27
% 0.13/0.41  # Proof object conjectures             : 33
% 0.13/0.41  # Proof object clause conjectures      : 30
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 21
% 0.13/0.41  # Proof object initial formulas used   : 13
% 0.13/0.41  # Proof object generating inferences   : 23
% 0.13/0.41  # Proof object simplifying inferences  : 32
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 16
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 35
% 0.13/0.41  # Removed in clause preprocessing      : 0
% 0.13/0.41  # Initial clauses in saturation        : 35
% 0.13/0.41  # Processed clauses                    : 480
% 0.13/0.41  # ...of these trivial                  : 3
% 0.13/0.41  # ...subsumed                          : 202
% 0.13/0.41  # ...remaining for further processing  : 275
% 0.13/0.41  # Other redundant clauses eliminated   : 9
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 16
% 0.13/0.41  # Backward-rewritten                   : 105
% 0.13/0.41  # Generated clauses                    : 902
% 0.13/0.41  # ...of the previous two non-trivial   : 830
% 0.13/0.41  # Contextual simplify-reflections      : 6
% 0.13/0.41  # Paramodulations                      : 879
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 23
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 118
% 0.13/0.41  #    Positive orientable unit clauses  : 12
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 1
% 0.13/0.41  #    Non-unit-clauses                  : 105
% 0.13/0.41  # Current number of unprocessed clauses: 409
% 0.13/0.41  # ...number of literals in the above   : 1973
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 156
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 8210
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 2771
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 220
% 0.13/0.41  # Unit Clause-clause subsumption calls : 179
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 23
% 0.13/0.41  # BW rewrite match successes           : 2
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 16841
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.060 s
% 0.20/0.41  # System time              : 0.008 s
% 0.20/0.41  # Total time               : 0.068 s
% 0.20/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
