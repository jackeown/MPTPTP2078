%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:18 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  152 (4911 expanded)
%              Number of clauses        :  112 (2239 expanded)
%              Number of leaves         :   20 (1207 expanded)
%              Depth                    :   20
%              Number of atoms          :  458 (20114 expanded)
%              Number of equality atoms :  170 (6056 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t8_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(c_0_20,plain,(
    ! [X19] :
      ( ( r1_xboole_0(X19,X19)
        | X19 != k1_xboole_0 )
      & ( X19 = k1_xboole_0
        | ~ r1_xboole_0(X19,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_funct_2])).

fof(c_0_22,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_23,plain,(
    ! [X46,X47,X48] :
      ( ~ v1_relat_1(X48)
      | ~ r1_tarski(k1_relat_1(X48),X46)
      | ~ r1_tarski(k2_relat_1(X48),X47)
      | m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( ( k2_zfmisc_1(X20,X21) != k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X49,X50,X51] :
      ( ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X50 = k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X49 = k1_relset_1(X49,X50,X51)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X49 != k1_relset_1(X49,X50,X51)
        | v1_funct_2(X51,X49,X50)
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( ~ v1_funct_2(X51,X49,X50)
        | X51 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( X51 != k1_xboole_0
        | v1_funct_2(X51,X49,X50)
        | X49 = k1_xboole_0
        | X50 != k1_xboole_0
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_28,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & r1_tarski(k2_relset_1(esk3_0,esk4_0,esk6_0),esk5_0)
    & ( esk4_0 != k1_xboole_0
      | esk3_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk6_0)
      | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_29,plain,(
    ! [X40,X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k1_relset_1(X40,X41,X42) = k1_relat_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | v1_relat_1(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_41,plain,(
    ! [X29,X30] : v1_relat_1(k2_zfmisc_1(X29,X30)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_42,plain,
    ( ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_45,plain,(
    ! [X34] :
      ( ( k1_relat_1(X34) != k1_xboole_0
        | k2_relat_1(X34) = k1_xboole_0
        | ~ v1_relat_1(X34) )
      & ( k2_relat_1(X34) != k1_xboole_0
        | k1_relat_1(X34) = k1_xboole_0
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_50,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_53,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_37]),c_0_51])])).

cnf(c_0_58,plain,
    ( k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

fof(c_0_60,plain,(
    ! [X27,X28] :
      ( ( ~ v4_relat_1(X28,X27)
        | r1_tarski(k1_relat_1(X28),X27)
        | ~ v1_relat_1(X28) )
      & ( ~ r1_tarski(k1_relat_1(X28),X27)
        | v4_relat_1(X28,X27)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_61,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k2_relset_1(X43,X44,X45) = k2_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_62,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_57]),c_0_54])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk6_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_69,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,X1)
    | ~ v4_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_56]),c_0_57])])).

cnf(c_0_70,plain,
    ( v4_relat_1(X1,X2)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_53]),c_0_54])])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk3_0,esk4_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_37])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = esk6_0
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,X1)
    | k2_relat_1(esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_57])])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k2_relat_1(esk6_0) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_56]),c_0_57])]),c_0_71])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_79,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_81,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 = esk6_0
    | esk4_0 = k1_xboole_0
    | k2_relat_1(esk6_0) != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_86,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = esk6_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_59])).

cnf(c_0_88,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_83])).

cnf(c_0_89,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_54])).

cnf(c_0_90,plain,
    ( k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),esk5_0)
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_47])).

cnf(c_0_92,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_93,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_37])).

cnf(c_0_94,plain,
    ( v4_relat_1(X1,k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_43])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 = esk6_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_87]),c_0_83])).

cnf(c_0_96,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_53]),c_0_54])]),c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),X1)
    | k2_relat_1(esk5_0) != k1_xboole_0
    | ~ v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( ~ v1_funct_1(esk6_0)
    | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X2),X3)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_31])).

cnf(c_0_101,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k1_relat_1(X3),X1)
    | ~ r1_tarski(k2_relat_1(X3),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_31])).

fof(c_0_102,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | r1_tarski(k7_relat_1(X36,X35),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_103,negated_conjecture,
    ( esk3_0 = esk6_0
    | esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_87]),c_0_83]),c_0_44])])).

cnf(c_0_104,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_64])).

cnf(c_0_105,negated_conjecture,
    ( esk3_0 = esk6_0
    | v4_relat_1(esk6_0,k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_106,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_83])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | k2_relat_1(esk5_0) != k1_xboole_0
    | ~ v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_57])])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])])).

cnf(c_0_109,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,k1_relat_1(X2),X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101])]),c_0_84])])).

fof(c_0_110,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | k2_relat_1(k7_relat_1(X32,X31)) = k9_relat_1(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_111,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_112,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_83])).

cnf(c_0_113,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_64])).

cnf(c_0_114,negated_conjecture,
    ( esk3_0 = esk6_0
    | r1_tarski(esk6_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_47])).

cnf(c_0_115,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk3_0 = esk6_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_57])])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,X2)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_90,c_0_47])).

cnf(c_0_117,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_118,negated_conjecture,
    ( v4_relat_1(esk6_0,X1)
    | k2_relat_1(esk5_0) != k1_xboole_0
    | ~ v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_119,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ r1_tarski(k1_relat_1(esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_31]),c_0_57]),c_0_80])])).

cnf(c_0_120,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,X1)
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_56]),c_0_57])])).

fof(c_0_121,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | k9_relat_1(X33,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

cnf(c_0_122,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_123,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_111]),c_0_112])])).

cnf(c_0_124,negated_conjecture,
    ( k1_relat_1(X1) = esk6_0
    | esk3_0 = esk6_0
    | esk3_0 != k1_xboole_0
    | ~ v4_relat_1(X1,esk6_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_125,negated_conjecture,
    ( esk3_0 = esk6_0
    | v4_relat_1(esk6_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_115]),c_0_57]),c_0_54])])).

cnf(c_0_126,plain,
    ( X1 = k1_relat_1(X2)
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v4_relat_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_116])).

cnf(c_0_127,negated_conjecture,
    ( v4_relat_1(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_37])).

cnf(c_0_128,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_129,plain,
    ( r1_xboole_0(X1,X2)
    | k2_relat_1(X2) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_90,c_0_117])).

cnf(c_0_130,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | k2_relat_1(esk5_0) != k1_xboole_0
    | ~ v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_118]),c_0_57])])).

cnf(c_0_131,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(k1_relat_1(esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_80])])).

cnf(c_0_132,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_133,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k2_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_112])])).

cnf(c_0_134,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk6_0
    | esk3_0 = esk6_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_57])])).

cnf(c_0_135,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0
    | k2_relat_1(esk3_0) != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_57])])).

cnf(c_0_136,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_137,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k2_relat_1(esk5_0) != k1_xboole_0
    | ~ v1_relat_1(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_130]),c_0_71])).

cnf(c_0_138,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_56]),c_0_84])])).

cnf(c_0_139,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_112])])).

cnf(c_0_140,negated_conjecture,
    ( esk3_0 = esk6_0
    | k2_relat_1(esk3_0) != k1_xboole_0
    | ~ v1_relat_1(esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_135]),c_0_136])).

cnf(c_0_141,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_139]),c_0_112])]),c_0_71])).

cnf(c_0_142,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_143,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_139]),c_0_112]),c_0_54])])).

cnf(c_0_144,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_141]),c_0_141]),c_0_139]),c_0_141]),c_0_112])])).

cnf(c_0_145,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_142]),c_0_43])).

cnf(c_0_146,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_43])).

cnf(c_0_147,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_106,c_0_143])).

cnf(c_0_148,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_141]),c_0_141]),c_0_43]),c_0_144]),c_0_144]),c_0_143])])).

cnf(c_0_149,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_101]),c_0_146]),c_0_89])).

cnf(c_0_150,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_147]),c_0_112])])).

cnf(c_0_151,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_149]),c_0_112]),c_0_150]),c_0_54]),c_0_139]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:44:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.54  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.38/0.54  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.38/0.54  #
% 0.38/0.54  # Preprocessing time       : 0.028 s
% 0.38/0.54  
% 0.38/0.54  # Proof found!
% 0.38/0.54  # SZS status Theorem
% 0.38/0.54  # SZS output start CNFRefutation
% 0.38/0.54  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.38/0.54  fof(t8_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 0.38/0.54  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.38/0.54  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.38/0.54  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.38/0.54  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.38/0.54  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.38/0.54  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.38/0.54  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.38/0.54  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.38/0.54  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.38/0.54  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.38/0.54  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.38/0.54  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.38/0.54  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.38/0.54  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.38/0.54  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.38/0.54  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.38/0.54  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.38/0.54  fof(t149_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 0.38/0.54  fof(c_0_20, plain, ![X19]:((r1_xboole_0(X19,X19)|X19!=k1_xboole_0)&(X19=k1_xboole_0|~r1_xboole_0(X19,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.38/0.54  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t8_funct_2])).
% 0.38/0.54  fof(c_0_22, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|~v1_xboole_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.38/0.54  fof(c_0_23, plain, ![X46, X47, X48]:(~v1_relat_1(X48)|(~r1_tarski(k1_relat_1(X48),X46)|~r1_tarski(k2_relat_1(X48),X47)|m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.38/0.54  fof(c_0_24, plain, ![X20, X21]:((k2_zfmisc_1(X20,X21)!=k1_xboole_0|(X20=k1_xboole_0|X21=k1_xboole_0))&((X20!=k1_xboole_0|k2_zfmisc_1(X20,X21)=k1_xboole_0)&(X21!=k1_xboole_0|k2_zfmisc_1(X20,X21)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.38/0.54  fof(c_0_25, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.38/0.54  cnf(c_0_26, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.54  fof(c_0_27, plain, ![X49, X50, X51]:((((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X50=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))&((~v1_funct_2(X51,X49,X50)|X49=k1_relset_1(X49,X50,X51)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X49!=k1_relset_1(X49,X50,X51)|v1_funct_2(X51,X49,X50)|X49!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))))&((~v1_funct_2(X51,X49,X50)|X51=k1_xboole_0|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(X51!=k1_xboole_0|v1_funct_2(X51,X49,X50)|X49=k1_xboole_0|X50!=k1_xboole_0|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.38/0.54  fof(c_0_28, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r1_tarski(k2_relset_1(esk3_0,esk4_0,esk6_0),esk5_0)&((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&(~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.38/0.54  fof(c_0_29, plain, ![X40, X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|k1_relset_1(X40,X41,X42)=k1_relat_1(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.38/0.54  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.54  cnf(c_0_31, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.38/0.54  cnf(c_0_32, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.54  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.54  cnf(c_0_34, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_26])).
% 0.38/0.54  fof(c_0_35, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.38/0.54  cnf(c_0_36, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.54  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.54  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.54  cnf(c_0_39, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.38/0.54  fof(c_0_40, plain, ![X25, X26]:(~v1_relat_1(X25)|(~m1_subset_1(X26,k1_zfmisc_1(X25))|v1_relat_1(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.38/0.54  fof(c_0_41, plain, ![X29, X30]:v1_relat_1(k2_zfmisc_1(X29,X30)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.38/0.54  cnf(c_0_42, plain, (~v1_relat_1(X1)|~v1_xboole_0(k2_zfmisc_1(X2,X3))|~r2_hidden(X4,X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.38/0.54  cnf(c_0_43, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_32])).
% 0.38/0.54  cnf(c_0_44, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.38/0.54  fof(c_0_45, plain, ![X34]:((k1_relat_1(X34)!=k1_xboole_0|k2_relat_1(X34)=k1_xboole_0|~v1_relat_1(X34))&(k2_relat_1(X34)!=k1_xboole_0|k1_relat_1(X34)=k1_xboole_0|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.38/0.54  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.38/0.54  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.54  cnf(c_0_48, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.38/0.54  cnf(c_0_49, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.38/0.54  cnf(c_0_50, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.38/0.54  cnf(c_0_51, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.38/0.54  cnf(c_0_52, plain, (~v1_relat_1(X1)|~r2_hidden(X2,X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(k2_relat_1(X1),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.38/0.54  cnf(c_0_53, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.54  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.38/0.54  cnf(c_0_55, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.38/0.54  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.38/0.54  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_37]), c_0_51])])).
% 0.38/0.54  cnf(c_0_58, plain, (k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X2,X1)|~r1_tarski(k2_relat_1(X1),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.38/0.54  cnf(c_0_59, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.38/0.54  fof(c_0_60, plain, ![X27, X28]:((~v4_relat_1(X28,X27)|r1_tarski(k1_relat_1(X28),X27)|~v1_relat_1(X28))&(~r1_tarski(k1_relat_1(X28),X27)|v4_relat_1(X28,X27)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.38/0.54  fof(c_0_61, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k2_relset_1(X43,X44,X45)=k2_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.38/0.54  fof(c_0_62, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.38/0.54  cnf(c_0_63, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_57]), c_0_54])])).
% 0.38/0.54  cnf(c_0_64, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.38/0.54  cnf(c_0_65, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.38/0.54  cnf(c_0_66, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.38/0.54  cnf(c_0_67, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.38/0.54  cnf(c_0_68, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk6_0,X1)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_47])).
% 0.38/0.54  cnf(c_0_69, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,X1)|~v4_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_56]), c_0_57])])).
% 0.38/0.54  cnf(c_0_70, plain, (v4_relat_1(X1,X2)|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_53]), c_0_54])])).
% 0.38/0.54  cnf(c_0_71, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.54  cnf(c_0_72, negated_conjecture, (r1_tarski(k2_relset_1(esk3_0,esk4_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.54  cnf(c_0_73, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_37])).
% 0.38/0.54  cnf(c_0_74, negated_conjecture, (esk4_0=k1_xboole_0|X1=esk6_0|esk3_0!=k1_xboole_0|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.38/0.54  cnf(c_0_75, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,X1)|k2_relat_1(esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_57])])).
% 0.38/0.54  cnf(c_0_76, negated_conjecture, (esk3_0=k1_xboole_0|k2_relat_1(esk6_0)!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_56]), c_0_57])]), c_0_71])).
% 0.38/0.54  cnf(c_0_77, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.38/0.54  cnf(c_0_78, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.38/0.54  cnf(c_0_79, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.38/0.54  cnf(c_0_80, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.38/0.54  fof(c_0_81, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.38/0.54  cnf(c_0_82, negated_conjecture, (esk3_0=esk6_0|esk4_0=k1_xboole_0|k2_relat_1(esk6_0)!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.38/0.54  cnf(c_0_83, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_77])).
% 0.38/0.54  cnf(c_0_84, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_78])).
% 0.38/0.54  cnf(c_0_85, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.38/0.54  cnf(c_0_86, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.38/0.54  cnf(c_0_87, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=esk6_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_59])).
% 0.38/0.54  cnf(c_0_88, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_83])).
% 0.38/0.54  cnf(c_0_89, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_54])).
% 0.38/0.54  cnf(c_0_90, plain, (k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_84])).
% 0.38/0.54  cnf(c_0_91, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),esk5_0)|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_85, c_0_47])).
% 0.38/0.54  cnf(c_0_92, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.54  cnf(c_0_93, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_37])).
% 0.38/0.54  cnf(c_0_94, plain, (v4_relat_1(X1,k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_86, c_0_43])).
% 0.38/0.54  cnf(c_0_95, negated_conjecture, (esk3_0=esk6_0|m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_87]), c_0_83])).
% 0.38/0.54  cnf(c_0_96, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_53]), c_0_54])]), c_0_89])).
% 0.38/0.54  cnf(c_0_97, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),X1)|k2_relat_1(esk5_0)!=k1_xboole_0|~v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.38/0.54  cnf(c_0_98, negated_conjecture, (~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.54  cnf(c_0_99, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.54  cnf(c_0_100, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X2),X3)|~r1_tarski(k2_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_92, c_0_31])).
% 0.38/0.54  cnf(c_0_101, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~v1_relat_1(X3)|~r1_tarski(k1_relat_1(X3),X1)|~r1_tarski(k2_relat_1(X3),X2)), inference(spm,[status(thm)],[c_0_39, c_0_31])).
% 0.38/0.54  fof(c_0_102, plain, ![X35, X36]:(~v1_relat_1(X36)|r1_tarski(k7_relat_1(X36,X35),X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.38/0.54  cnf(c_0_103, negated_conjecture, (esk3_0=esk6_0|esk3_0!=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_87]), c_0_83]), c_0_44])])).
% 0.38/0.54  cnf(c_0_104, plain, (k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_64])).
% 0.38/0.54  cnf(c_0_105, negated_conjecture, (esk3_0=esk6_0|v4_relat_1(esk6_0,k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.38/0.54  cnf(c_0_106, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_86, c_0_83])).
% 0.38/0.54  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|k2_relat_1(esk5_0)!=k1_xboole_0|~v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_57])])).
% 0.38/0.54  cnf(c_0_108, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])])).
% 0.38/0.54  cnf(c_0_109, plain, (X1=k1_xboole_0|v1_funct_2(X2,k1_relat_1(X2),X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101])]), c_0_84])])).
% 0.38/0.54  fof(c_0_110, plain, ![X31, X32]:(~v1_relat_1(X32)|k2_relat_1(k7_relat_1(X32,X31))=k9_relat_1(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.38/0.54  cnf(c_0_111, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.38/0.54  cnf(c_0_112, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_83])).
% 0.38/0.54  cnf(c_0_113, plain, (X1=k1_relat_1(X2)|~v4_relat_1(X2,X1)|~v1_relat_1(X2)|~r1_tarski(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_67, c_0_64])).
% 0.38/0.54  cnf(c_0_114, negated_conjecture, (esk3_0=esk6_0|r1_tarski(esk6_0,X1)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_47])).
% 0.38/0.54  cnf(c_0_115, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk3_0=esk6_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_57])])).
% 0.38/0.54  cnf(c_0_116, plain, (r1_tarski(X1,X2)|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_90, c_0_47])).
% 0.38/0.54  cnf(c_0_117, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.38/0.54  cnf(c_0_118, negated_conjecture, (v4_relat_1(esk6_0,X1)|k2_relat_1(esk5_0)!=k1_xboole_0|~v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 0.38/0.54  cnf(c_0_119, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~r1_tarski(k1_relat_1(esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_31]), c_0_57]), c_0_80])])).
% 0.38/0.54  cnf(c_0_120, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,X1)|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_56]), c_0_57])])).
% 0.38/0.54  fof(c_0_121, plain, ![X33]:(~v1_relat_1(X33)|k9_relat_1(X33,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).
% 0.38/0.54  cnf(c_0_122, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.38/0.54  cnf(c_0_123, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_111]), c_0_112])])).
% 0.38/0.54  cnf(c_0_124, negated_conjecture, (k1_relat_1(X1)=esk6_0|esk3_0=esk6_0|esk3_0!=k1_xboole_0|~v4_relat_1(X1,esk6_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.38/0.54  cnf(c_0_125, negated_conjecture, (esk3_0=esk6_0|v4_relat_1(esk6_0,X1)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_115]), c_0_57]), c_0_54])])).
% 0.38/0.54  cnf(c_0_126, plain, (X1=k1_relat_1(X2)|k2_relat_1(X1)!=k1_xboole_0|~v4_relat_1(X2,X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_113, c_0_116])).
% 0.38/0.54  cnf(c_0_127, negated_conjecture, (v4_relat_1(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_86, c_0_37])).
% 0.38/0.54  cnf(c_0_128, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.54  cnf(c_0_129, plain, (r1_xboole_0(X1,X2)|k2_relat_1(X2)!=k1_xboole_0|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_90, c_0_117])).
% 0.38/0.54  cnf(c_0_130, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|k2_relat_1(esk5_0)!=k1_xboole_0|~v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_118]), c_0_57])])).
% 0.38/0.54  cnf(c_0_131, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|~r1_tarski(k1_relat_1(esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_80])])).
% 0.38/0.54  cnf(c_0_132, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.38/0.54  cnf(c_0_133, plain, (k9_relat_1(k1_xboole_0,X1)=k2_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_112])])).
% 0.38/0.54  cnf(c_0_134, negated_conjecture, (k1_relat_1(esk6_0)=esk6_0|esk3_0=esk6_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_57])])).
% 0.38/0.54  cnf(c_0_135, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0|k2_relat_1(esk3_0)!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126, c_0_127]), c_0_57])])).
% 0.38/0.54  cnf(c_0_136, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 0.38/0.54  cnf(c_0_137, negated_conjecture, (esk3_0=k1_xboole_0|k2_relat_1(esk5_0)!=k1_xboole_0|~v1_relat_1(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_130]), c_0_71])).
% 0.38/0.54  cnf(c_0_138, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_56]), c_0_84])])).
% 0.38/0.54  cnf(c_0_139, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_112])])).
% 0.38/0.54  cnf(c_0_140, negated_conjecture, (esk3_0=esk6_0|k2_relat_1(esk3_0)!=k1_xboole_0|~v1_relat_1(esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_134, c_0_135]), c_0_136])).
% 0.38/0.54  cnf(c_0_141, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_139]), c_0_112])]), c_0_71])).
% 0.38/0.54  cnf(c_0_142, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.54  cnf(c_0_143, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_139]), c_0_112]), c_0_54])])).
% 0.38/0.54  cnf(c_0_144, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_141]), c_0_141]), c_0_139]), c_0_141]), c_0_112])])).
% 0.38/0.54  cnf(c_0_145, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_142]), c_0_43])).
% 0.38/0.54  cnf(c_0_146, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_43])).
% 0.38/0.54  cnf(c_0_147, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_106, c_0_143])).
% 0.38/0.54  cnf(c_0_148, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_141]), c_0_141]), c_0_43]), c_0_144]), c_0_144]), c_0_143])])).
% 0.38/0.54  cnf(c_0_149, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(k2_relat_1(X1),X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_101]), c_0_146]), c_0_89])).
% 0.38/0.54  cnf(c_0_150, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_147]), c_0_112])])).
% 0.38/0.54  cnf(c_0_151, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_149]), c_0_112]), c_0_150]), c_0_54]), c_0_139]), c_0_54])]), ['proof']).
% 0.38/0.54  # SZS output end CNFRefutation
% 0.38/0.54  # Proof object total steps             : 152
% 0.38/0.54  # Proof object clause steps            : 112
% 0.38/0.54  # Proof object formula steps           : 40
% 0.38/0.54  # Proof object conjectures             : 52
% 0.38/0.54  # Proof object clause conjectures      : 49
% 0.38/0.54  # Proof object formula conjectures     : 3
% 0.38/0.54  # Proof object initial clauses used    : 34
% 0.38/0.54  # Proof object initial formulas used   : 20
% 0.38/0.54  # Proof object generating inferences   : 69
% 0.38/0.54  # Proof object simplifying inferences  : 102
% 0.38/0.54  # Training examples: 0 positive, 0 negative
% 0.38/0.54  # Parsed axioms                        : 20
% 0.38/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.54  # Initial clauses                      : 42
% 0.38/0.54  # Removed in clause preprocessing      : 0
% 0.38/0.54  # Initial clauses in saturation        : 42
% 0.38/0.54  # Processed clauses                    : 3357
% 0.38/0.54  # ...of these trivial                  : 14
% 0.38/0.54  # ...subsumed                          : 2730
% 0.38/0.54  # ...remaining for further processing  : 613
% 0.38/0.54  # Other redundant clauses eliminated   : 11
% 0.38/0.54  # Clauses deleted for lack of memory   : 0
% 0.38/0.54  # Backward-subsumed                    : 86
% 0.38/0.54  # Backward-rewritten                   : 363
% 0.38/0.54  # Generated clauses                    : 7682
% 0.38/0.54  # ...of the previous two non-trivial   : 6907
% 0.38/0.54  # Contextual simplify-reflections      : 30
% 0.38/0.54  # Paramodulations                      : 7672
% 0.38/0.54  # Factorizations                       : 0
% 0.38/0.54  # Equation resolutions                 : 11
% 0.38/0.54  # Propositional unsat checks           : 0
% 0.38/0.54  #    Propositional check models        : 0
% 0.38/0.54  #    Propositional check unsatisfiable : 0
% 0.38/0.54  #    Propositional clauses             : 0
% 0.38/0.54  #    Propositional clauses after purity: 0
% 0.38/0.54  #    Propositional unsat core size     : 0
% 0.38/0.54  #    Propositional preprocessing time  : 0.000
% 0.38/0.54  #    Propositional encoding time       : 0.000
% 0.38/0.54  #    Propositional solver time         : 0.000
% 0.38/0.54  #    Success case prop preproc time    : 0.000
% 0.38/0.54  #    Success case prop encoding time   : 0.000
% 0.38/0.54  #    Success case prop solver time     : 0.000
% 0.38/0.54  # Current number of processed clauses  : 155
% 0.38/0.54  #    Positive orientable unit clauses  : 20
% 0.38/0.54  #    Positive unorientable unit clauses: 0
% 0.38/0.54  #    Negative unit clauses             : 2
% 0.38/0.54  #    Non-unit-clauses                  : 133
% 0.38/0.54  # Current number of unprocessed clauses: 3372
% 0.38/0.54  # ...number of literals in the above   : 17928
% 0.38/0.54  # Current number of archived formulas  : 0
% 0.38/0.54  # Current number of archived clauses   : 449
% 0.38/0.54  # Clause-clause subsumption calls (NU) : 40696
% 0.38/0.54  # Rec. Clause-clause subsumption calls : 16062
% 0.38/0.54  # Non-unit clause-clause subsumptions  : 2679
% 0.38/0.54  # Unit Clause-clause subsumption calls : 195
% 0.38/0.54  # Rewrite failures with RHS unbound    : 0
% 0.38/0.54  # BW rewrite match attempts            : 15
% 0.38/0.54  # BW rewrite match successes           : 8
% 0.38/0.54  # Condensation attempts                : 0
% 0.38/0.54  # Condensation successes               : 0
% 0.38/0.54  # Termbank termtop insertions          : 101289
% 0.38/0.54  
% 0.38/0.54  # -------------------------------------------------
% 0.38/0.54  # User time                : 0.194 s
% 0.38/0.54  # System time              : 0.006 s
% 0.38/0.54  # Total time               : 0.201 s
% 0.38/0.54  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
