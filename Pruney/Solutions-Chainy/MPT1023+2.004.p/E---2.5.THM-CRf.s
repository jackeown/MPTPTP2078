%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:22 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 (3951 expanded)
%              Number of clauses        :   86 (1578 expanded)
%              Number of leaves         :   14 ( 950 expanded)
%              Depth                    :   23
%              Number of atoms          :  338 (22407 expanded)
%              Number of equality atoms :  116 (5216 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X47,X48,X49] :
      ( ( ~ v1_funct_2(X49,X47,X48)
        | X47 = k1_relset_1(X47,X48,X49)
        | X48 = k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X47 != k1_relset_1(X47,X48,X49)
        | v1_funct_2(X49,X47,X48)
        | X48 = k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( ~ v1_funct_2(X49,X47,X48)
        | X47 = k1_relset_1(X47,X48,X49)
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X47 != k1_relset_1(X47,X48,X49)
        | v1_funct_2(X49,X47,X48)
        | X47 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( ~ v1_funct_2(X49,X47,X48)
        | X49 = k1_xboole_0
        | X47 = k1_xboole_0
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( X49 != k1_xboole_0
        | v1_funct_2(X49,X47,X48)
        | X47 = k1_xboole_0
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_16,negated_conjecture,(
    ! [X54] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & v1_funct_1(esk9_0)
      & v1_funct_2(esk9_0,esk6_0,esk7_0)
      & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & ( ~ m1_subset_1(X54,esk6_0)
        | k1_funct_1(esk8_0,X54) = k1_funct_1(esk9_0,X54) )
      & ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_18,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,plain,(
    ! [X25,X26] :
      ( ( r2_hidden(esk3_2(X25,X26),k1_relat_1(X25))
        | k1_relat_1(X25) != k1_relat_1(X26)
        | X25 = X26
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k1_funct_1(X25,esk3_2(X25,X26)) != k1_funct_1(X26,esk3_2(X25,X26))
        | k1_relat_1(X25) != k1_relat_1(X26)
        | X25 = X26
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_24,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

fof(c_0_34,plain,(
    ! [X21,X22] :
      ( ( ~ m1_subset_1(X21,k1_zfmisc_1(X22))
        | r1_tarski(X21,X22) )
      & ( ~ r1_tarski(X21,X22)
        | m1_subset_1(X21,k1_zfmisc_1(X22)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

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
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | m1_subset_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_37,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | X1 = esk9_0
    | r2_hidden(esk3_2(X1,esk9_0),k1_relat_1(X1))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_32])]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_41,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk3_2(X1,X2)) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_42,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | X1 = esk9_0
    | k1_funct_1(X1,esk3_2(X1,esk9_0)) != k1_funct_1(esk9_0,esk3_2(X1,esk9_0))
    | k1_relat_1(X1) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk8_0,X1) = k1_funct_1(esk9_0,X1)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_51,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk9_0 = esk8_0
    | m1_subset_1(esk3_2(esk8_0,esk9_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk7_0 = k1_xboole_0
    | k1_funct_1(esk9_0,esk3_2(esk8_0,esk9_0)) != k1_funct_1(esk8_0,esk3_2(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_53,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ r2_relset_1(X37,X38,X39,X40)
        | X39 = X40
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != X40
        | r2_relset_1(X37,X38,X39,X40)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_56,plain,(
    ! [X31,X32,X33] :
      ( ( v4_relat_1(X33,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v5_relat_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk7_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_59,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_62,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_63,plain,(
    ! [X23,X24] :
      ( ( ~ v4_relat_1(X24,X23)
        | r1_tarski(k1_relat_1(X24),X23)
        | ~ v1_relat_1(X24) )
      & ( ~ r1_tarski(k1_relat_1(X24),X23)
        | v4_relat_1(X24,X23)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_64,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( esk9_0 = esk8_0
    | v1_funct_2(esk8_0,esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( esk9_0 = esk8_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_58])).

cnf(c_0_68,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_62])).

cnf(c_0_73,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk6_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( r2_relset_1(esk6_0,esk7_0,esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_27])).

cnf(c_0_77,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_79,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_80,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_79]),c_0_80])])).

cnf(c_0_83,negated_conjecture,
    ( v4_relat_1(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_27])).

cnf(c_0_84,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk2_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_70])).

cnf(c_0_85,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_funct_2(esk9_0,esk6_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_82])).

cnf(c_0_86,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_83]),c_0_40])])).

cnf(c_0_88,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_84])).

cnf(c_0_89,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( esk9_0 = esk8_0
    | m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_58])).

cnf(c_0_92,negated_conjecture,
    ( v4_relat_1(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_19])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk1_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( esk9_0 = esk8_0
    | esk9_0 = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_92]),c_0_31])])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | r2_hidden(esk1_1(k1_relat_1(esk8_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | ~ r2_relset_1(esk6_0,esk7_0,k1_xboole_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_79])).

cnf(c_0_99,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_95]),c_0_76])])).

cnf(c_0_100,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_62])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | r2_hidden(esk1_1(k1_relat_1(esk9_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_94])).

cnf(c_0_105,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_55])])).

cnf(c_0_106,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0
    | ~ v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( esk8_0 = X1
    | r2_hidden(esk3_2(esk8_0,X1),k1_xboole_0)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_105]),c_0_39]),c_0_40])])).

cnf(c_0_108,negated_conjecture,
    ( k1_relat_1(esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_103]),c_0_55])])).

cnf(c_0_109,negated_conjecture,
    ( esk9_0 = esk8_0
    | r2_hidden(esk3_2(esk8_0,esk9_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_30]),c_0_31])])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_relset_1(k1_xboole_0,esk7_0,esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( esk9_0 = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_109]),c_0_55])])).

cnf(c_0_112,negated_conjecture,
    ( r2_relset_1(k1_xboole_0,esk7_0,esk8_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_103])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.41  # and selection function SelectNewComplexAHP.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t113_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 0.20/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.41  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.41  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.41  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.20/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.20/0.41  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t113_funct_2])).
% 0.20/0.41  fof(c_0_15, plain, ![X47, X48, X49]:((((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X48=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))&((~v1_funct_2(X49,X47,X48)|X47=k1_relset_1(X47,X48,X49)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X47!=k1_relset_1(X47,X48,X49)|v1_funct_2(X49,X47,X48)|X47!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))))&((~v1_funct_2(X49,X47,X48)|X49=k1_xboole_0|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(X49!=k1_xboole_0|v1_funct_2(X49,X47,X48)|X47=k1_xboole_0|X48!=k1_xboole_0|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.41  fof(c_0_16, negated_conjecture, ![X54]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((~m1_subset_1(X54,esk6_0)|k1_funct_1(esk8_0,X54)=k1_funct_1(esk9_0,X54))&~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])])).
% 0.20/0.41  fof(c_0_17, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k1_relset_1(X34,X35,X36)=k1_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.41  cnf(c_0_18, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  fof(c_0_22, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.41  fof(c_0_23, plain, ![X25, X26]:((r2_hidden(esk3_2(X25,X26),k1_relat_1(X25))|k1_relat_1(X25)!=k1_relat_1(X26)|X25=X26|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k1_funct_1(X25,esk3_2(X25,X26))!=k1_funct_1(X26,esk3_2(X25,X26))|k1_relat_1(X25)!=k1_relat_1(X26)|X25=X26|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.20/0.41  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_28, plain, (r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0|esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_26, c_0_19])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_27])).
% 0.20/0.41  fof(c_0_34, plain, ![X21, X22]:((~m1_subset_1(X21,k1_zfmisc_1(X22))|r1_tarski(X21,X22))&(~r1_tarski(X21,X22)|m1_subset_1(X21,k1_zfmisc_1(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  fof(c_0_35, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.41  fof(c_0_36, plain, ![X19, X20]:(~r2_hidden(X19,X20)|m1_subset_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (esk7_0=k1_xboole_0|X1=esk9_0|r2_hidden(esk3_2(X1,esk9_0),k1_relat_1(X1))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_32])]), c_0_33])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_41, plain, (X1=X2|k1_funct_1(X1,esk3_2(X1,X2))!=k1_funct_1(X2,esk3_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  fof(c_0_42, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.41  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_44, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_45, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (esk9_0=esk8_0|esk7_0=k1_xboole_0|r2_hidden(esk3_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (esk7_0=k1_xboole_0|X1=esk9_0|k1_funct_1(X1,esk3_2(X1,esk9_0))!=k1_funct_1(esk9_0,esk3_2(X1,esk9_0))|k1_relat_1(X1)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_30]), c_0_31])])).
% 0.20/0.41  cnf(c_0_48, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk2_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk8_0,X1)=k1_funct_1(esk9_0,X1)|~m1_subset_1(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (esk7_0=k1_xboole_0|esk9_0=esk8_0|m1_subset_1(esk3_2(esk8_0,esk9_0),esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (esk9_0=esk8_0|esk7_0=k1_xboole_0|k1_funct_1(esk9_0,esk3_2(esk8_0,esk9_0))!=k1_funct_1(esk8_0,esk3_2(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_38]), c_0_39]), c_0_40])])).
% 0.20/0.41  fof(c_0_53, plain, ![X37, X38, X39, X40]:((~r2_relset_1(X37,X38,X39,X40)|X39=X40|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(X39!=X40|r2_relset_1(X37,X38,X39,X40)|(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.20/0.41  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.41  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.41  fof(c_0_56, plain, ![X31, X32, X33]:((v4_relat_1(X33,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v5_relat_1(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.41  cnf(c_0_57, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (esk9_0=esk8_0|esk7_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.20/0.41  cnf(c_0_59, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.41  fof(c_0_60, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_62, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.41  fof(c_0_63, plain, ![X23, X24]:((~v4_relat_1(X24,X23)|r1_tarski(k1_relat_1(X24),X23)|~v1_relat_1(X24))&(~r1_tarski(k1_relat_1(X24),X23)|v4_relat_1(X24,X23)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.20/0.41  cnf(c_0_64, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.41  cnf(c_0_65, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (esk9_0=esk8_0|v1_funct_2(esk8_0,esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_58])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (esk9_0=esk8_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_27, c_0_58])).
% 0.20/0.41  cnf(c_0_68, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_59])).
% 0.20/0.41  cnf(c_0_69, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.41  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.41  cnf(c_0_71, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.20/0.41  cnf(c_0_72, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_62])).
% 0.20/0.41  cnf(c_0_73, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_62])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (~r2_relset_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (esk9_0=esk8_0|esk6_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (r2_relset_1(esk6_0,esk7_0,esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_68, c_0_27])).
% 0.20/0.41  cnf(c_0_77, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.41  cnf(c_0_78, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (esk8_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 0.20/0.41  cnf(c_0_80, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.20/0.41  cnf(c_0_81, plain, (X1=X2|r2_hidden(esk2_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_69, c_0_44])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_79]), c_0_80])])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (v4_relat_1(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_27])).
% 0.20/0.41  cnf(c_0_84, plain, (k1_xboole_0=X1|r2_hidden(esk2_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_81, c_0_70])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (esk6_0=k1_xboole_0|v1_funct_2(esk9_0,esk6_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_82])).
% 0.20/0.41  cnf(c_0_86, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_83]), c_0_40])])).
% 0.20/0.41  cnf(c_0_88, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_48, c_0_84])).
% 0.20/0.41  cnf(c_0_89, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, (esk6_0=k1_xboole_0|esk9_0=k1_xboole_0|~m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_65, c_0_85])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (esk9_0=esk8_0|m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_19, c_0_58])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (v4_relat_1(esk9_0,esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_19])).
% 0.20/0.41  cnf(c_0_93, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.20/0.41  cnf(c_0_94, plain, (k1_xboole_0=X1|r2_hidden(esk1_1(X1),X1)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (esk9_0=esk8_0|esk9_0=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (r1_tarski(k1_relat_1(esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_92]), c_0_31])])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|r2_hidden(esk1_1(k1_relat_1(esk8_0)),esk6_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.20/0.41  cnf(c_0_98, negated_conjecture, (esk6_0=k1_xboole_0|~r2_relset_1(esk6_0,esk7_0,k1_xboole_0,esk9_0)), inference(spm,[status(thm)],[c_0_74, c_0_79])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (esk6_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_95]), c_0_76])])).
% 0.20/0.41  cnf(c_0_100, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_68, c_0_62])).
% 0.20/0.41  cnf(c_0_101, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_86, c_0_96])).
% 0.20/0.41  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_97])).
% 0.20/0.41  cnf(c_0_103, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])])).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|r2_hidden(esk1_1(k1_relat_1(esk9_0)),esk6_0)), inference(spm,[status(thm)],[c_0_101, c_0_94])).
% 0.20/0.41  cnf(c_0_105, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_55])])).
% 0.20/0.41  cnf(c_0_106, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0|~v1_xboole_0(esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_104])).
% 0.20/0.41  cnf(c_0_107, negated_conjecture, (esk8_0=X1|r2_hidden(esk3_2(esk8_0,X1),k1_xboole_0)|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_105]), c_0_39]), c_0_40])])).
% 0.20/0.41  cnf(c_0_108, negated_conjecture, (k1_relat_1(esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_103]), c_0_55])])).
% 0.20/0.41  cnf(c_0_109, negated_conjecture, (esk9_0=esk8_0|r2_hidden(esk3_2(esk8_0,esk9_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_30]), c_0_31])])).
% 0.20/0.41  cnf(c_0_110, negated_conjecture, (~r2_relset_1(k1_xboole_0,esk7_0,esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_74, c_0_103])).
% 0.20/0.41  cnf(c_0_111, negated_conjecture, (esk9_0=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_109]), c_0_55])])).
% 0.20/0.41  cnf(c_0_112, negated_conjecture, (r2_relset_1(k1_xboole_0,esk7_0,esk8_0,esk8_0)), inference(rw,[status(thm)],[c_0_76, c_0_103])).
% 0.20/0.41  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_112])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 114
% 0.20/0.41  # Proof object clause steps            : 86
% 0.20/0.41  # Proof object formula steps           : 28
% 0.20/0.41  # Proof object conjectures             : 55
% 0.20/0.41  # Proof object clause conjectures      : 52
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 26
% 0.20/0.41  # Proof object initial formulas used   : 14
% 0.20/0.41  # Proof object generating inferences   : 53
% 0.20/0.41  # Proof object simplifying inferences  : 54
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 15
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 39
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 39
% 0.20/0.41  # Processed clauses                    : 607
% 0.20/0.41  # ...of these trivial                  : 41
% 0.20/0.41  # ...subsumed                          : 143
% 0.20/0.41  # ...remaining for further processing  : 423
% 0.20/0.41  # Other redundant clauses eliminated   : 9
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 15
% 0.20/0.41  # Backward-rewritten                   : 226
% 0.20/0.41  # Generated clauses                    : 1402
% 0.20/0.41  # ...of the previous two non-trivial   : 1349
% 0.20/0.41  # Contextual simplify-reflections      : 3
% 0.20/0.41  # Paramodulations                      : 1391
% 0.20/0.41  # Factorizations                       : 1
% 0.20/0.41  # Equation resolutions                 : 11
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 137
% 0.20/0.41  #    Positive orientable unit clauses  : 34
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 0
% 0.20/0.41  #    Non-unit-clauses                  : 103
% 0.20/0.41  # Current number of unprocessed clauses: 609
% 0.20/0.41  # ...number of literals in the above   : 1788
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 279
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 8354
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 5319
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 161
% 0.20/0.41  # Unit Clause-clause subsumption calls : 1124
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 62
% 0.20/0.41  # BW rewrite match successes           : 7
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 21004
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.074 s
% 0.20/0.41  # System time              : 0.002 s
% 0.20/0.41  # Total time               : 0.076 s
% 0.20/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
