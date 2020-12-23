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
% DateTime   : Thu Dec  3 11:07:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 161 expanded)
%              Number of clauses        :   36 (  65 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 843 expanded)
%              Number of equality atoms :   47 ( 191 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t142_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r1_partfun1(X3,X4)
           => ( ( X2 = k1_xboole_0
                & X1 != k1_xboole_0 )
              | r2_relset_1(X1,X2,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t148_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ( v1_partfun1(X3,X1)
              & v1_partfun1(X4,X1)
              & r1_partfun1(X3,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( r1_partfun1(X3,X4)
             => ( ( X2 = k1_xboole_0
                  & X1 != k1_xboole_0 )
                | r2_relset_1(X1,X2,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_2])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_partfun1(esk3_0,esk4_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ~ r2_relset_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( k2_zfmisc_1(X8,X9) != k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ v1_funct_1(X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ v1_funct_1(X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | ~ v1_partfun1(X25,X23)
      | ~ v1_partfun1(X26,X23)
      | ~ r1_partfun1(X25,X26)
      | X25 = X26 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).

fof(c_0_17,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( X1 = X4
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X4,X2)
    | ~ r1_partfun1(X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] :
      ( ( v1_funct_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | v1_xboole_0(X21) )
      & ( v1_partfun1(X22,X20)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_25,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_relset_1(X16,X17,X18,X19)
        | X18 = X19
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X18 != X19
        | r2_relset_1(X16,X17,X18,X19)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    | k1_xboole_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( X1 = esk4_0
    | ~ r1_partfun1(X1,esk4_0)
    | ~ v1_partfun1(esk4_0,esk1_0)
    | ~ v1_partfun1(X1,esk1_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( r1_partfun1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | k1_xboole_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = esk4_0
    | ~ v1_partfun1(esk4_0,esk1_0)
    | ~ v1_partfun1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_31]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( v1_partfun1(esk3_0,esk1_0)
    | v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_13]),c_0_34]),c_0_32])])).

cnf(c_0_42,negated_conjecture,
    ( v1_partfun1(esk4_0,esk1_0)
    | v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_21]),c_0_35]),c_0_23])])).

cnf(c_0_43,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ r2_relset_1(esk1_0,esk2_0,k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_39]),c_0_28])])).

fof(c_0_46,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_47,negated_conjecture,
    ( esk3_0 = esk4_0
    | v1_xboole_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r2_relset_1(esk1_0,esk2_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( r2_relset_1(esk1_0,esk2_0,esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ r2_relset_1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_47]),c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( k1_xboole_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_38]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_AE_CS_SP_PI_S0Y
% 0.13/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t142_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_relset_1(X1,X2,X3,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(t148_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((v1_funct_1(X4)&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_partfun1(X3,X1)&v1_partfun1(X4,X1))&r1_partfun1(X3,X4))=>X3=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.13/0.38  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_partfun1(X3,X4)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|r2_relset_1(X1,X2,X3,X4)))))), inference(assume_negation,[status(cth)],[t142_funct_2])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_partfun1(esk3_0,esk4_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&~r2_relset_1(esk1_0,esk2_0,esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X8, X9]:((k2_zfmisc_1(X8,X9)!=k1_xboole_0|(X8=k1_xboole_0|X9=k1_xboole_0))&((X8!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0)&(X9!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  fof(c_0_15, plain, ![X10]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  fof(c_0_16, plain, ![X23, X24, X25, X26]:(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|(~v1_funct_1(X26)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|(~v1_partfun1(X25,X23)|~v1_partfun1(X26,X23)|~r1_partfun1(X25,X26)|X25=X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_partfun1])])])).
% 0.13/0.38  fof(c_0_17, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|k1_xboole_0!=esk2_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_20, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_22, plain, (X1=X4|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_partfun1(X1,X2)|~v1_partfun1(X4,X2)|~r1_partfun1(X1,X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_24, plain, ![X20, X21, X22]:((v1_funct_1(X22)|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_xboole_0(X21))&(v1_partfun1(X22,X20)|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_xboole_0(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.13/0.38  fof(c_0_25, plain, ![X16, X17, X18, X19]:((~r2_relset_1(X16,X17,X18,X19)|X18=X19|(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&(X18!=X19|r2_relset_1(X16,X17,X18,X19)|(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.13/0.38  cnf(c_0_26, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)|k1_xboole_0!=esk2_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_20])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|k1_xboole_0!=esk2_0), inference(spm,[status(thm)],[c_0_21, c_0_14])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (X1=esk4_0|~r1_partfun1(X1,esk4_0)|~v1_partfun1(esk4_0,esk1_0)|~v1_partfun1(X1,esk1_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_21]), c_0_23])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r1_partfun1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_33, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_36, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (~r2_relset_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (esk3_0=k1_xboole_0|k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|k1_xboole_0!=esk2_0), inference(spm,[status(thm)],[c_0_18, c_0_29])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (esk3_0=esk4_0|~v1_partfun1(esk4_0,esk1_0)|~v1_partfun1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_13]), c_0_31]), c_0_32])])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v1_partfun1(esk3_0,esk1_0)|v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_13]), c_0_34]), c_0_32])])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (v1_partfun1(esk4_0,esk1_0)|v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_21]), c_0_35]), c_0_23])])).
% 0.13/0.38  cnf(c_0_43, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_36])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k1_xboole_0!=esk2_0|~r2_relset_1(esk1_0,esk2_0,k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (esk4_0=k1_xboole_0|k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_39]), c_0_28])])).
% 0.13/0.38  fof(c_0_46, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (esk3_0=esk4_0|v1_xboole_0(esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (r2_relset_1(esk1_0,esk2_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_21])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (r2_relset_1(esk1_0,esk2_0,esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_13])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k1_xboole_0!=esk2_0|~r2_relset_1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.38  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_47]), c_0_48])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k1_xboole_0!=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_38]), c_0_50])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 55
% 0.13/0.38  # Proof object clause steps            : 36
% 0.13/0.38  # Proof object formula steps           : 19
% 0.13/0.38  # Proof object conjectures             : 29
% 0.13/0.38  # Proof object clause conjectures      : 26
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 9
% 0.13/0.38  # Proof object generating inferences   : 19
% 0.13/0.38  # Proof object simplifying inferences  : 21
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 25
% 0.13/0.38  # Removed in clause preprocessing      : 1
% 0.13/0.38  # Initial clauses in saturation        : 24
% 0.13/0.38  # Processed clauses                    : 229
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 112
% 0.13/0.38  # ...remaining for further processing  : 116
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 5
% 0.13/0.38  # Generated clauses                    : 316
% 0.13/0.38  # ...of the previous two non-trivial   : 278
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 313
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 108
% 0.13/0.38  #    Positive orientable unit clauses  : 16
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 90
% 0.13/0.38  # Current number of unprocessed clauses: 73
% 0.13/0.38  # ...number of literals in the above   : 347
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 5
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1811
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 1013
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 42
% 0.13/0.38  # Unit Clause-clause subsumption calls : 78
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 20
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5204
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.041 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
