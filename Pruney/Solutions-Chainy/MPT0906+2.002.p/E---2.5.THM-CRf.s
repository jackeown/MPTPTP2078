%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:05 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  71 expanded)
%              Number of clauses        :   23 (  30 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   96 ( 197 expanded)
%              Number of equality atoms :   36 (  95 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) != k1_xboole_0
     => ! [X3] :
          ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
         => ( X3 != k1_mcart_1(X3)
            & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t26_mcart_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => ( X3 != k1_mcart_1(X3)
                & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) != k1_xboole_0
       => ! [X3] :
            ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
           => ( X3 != k1_mcart_1(X3)
              & X3 != k2_mcart_1(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t66_mcart_1])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,X11)
      | v1_xboole_0(X11)
      | r2_hidden(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_11,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) != k1_xboole_0
    & m1_subset_1(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))
    & ( esk4_0 = k1_mcart_1(esk4_0)
      | esk4_0 = k2_mcart_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ( X19 != k1_mcart_1(X19)
        | ~ m1_subset_1(X19,k2_zfmisc_1(X17,X18))
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X19 != k2_mcart_1(X19)
        | ~ m1_subset_1(X19,k2_zfmisc_1(X17,X18))
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_mcart_1])])])])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(k1_mcart_1(X14),X15)
        | ~ r2_hidden(X14,k2_zfmisc_1(X15,X16)) )
      & ( r2_hidden(k2_mcart_1(X14),X16)
        | ~ r2_hidden(X14,k2_zfmisc_1(X15,X16)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))
    | v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 != k2_mcart_1(X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = k1_mcart_1(esk4_0)
    | esk4_0 = k2_mcart_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 != k1_mcart_1(X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | ~ r1_tarski(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_24,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_25,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ m1_subset_1(esk4_0,k2_zfmisc_1(X2,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_14])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:42:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.19/0.37  # and selection function SelectNewComplexAHP.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t66_mcart_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)!=k1_xboole_0=>![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_mcart_1)).
% 0.19/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.37  fof(t26_mcart_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 0.19/0.37  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)!=k1_xboole_0=>![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3))))), inference(assume_negation,[status(cth)],[t66_mcart_1])).
% 0.19/0.37  fof(c_0_10, plain, ![X10, X11]:(~m1_subset_1(X10,X11)|(v1_xboole_0(X11)|r2_hidden(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.37  fof(c_0_11, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)!=k1_xboole_0&(m1_subset_1(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))&(esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.37  fof(c_0_12, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.37  cnf(c_0_13, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  fof(c_0_15, plain, ![X17, X18, X19]:((X19!=k1_mcart_1(X19)|~m1_subset_1(X19,k2_zfmisc_1(X17,X18))|(X17=k1_xboole_0|X18=k1_xboole_0))&(X19!=k2_mcart_1(X19)|~m1_subset_1(X19,k2_zfmisc_1(X17,X18))|(X17=k1_xboole_0|X18=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_mcart_1])])])])).
% 0.19/0.37  fof(c_0_16, plain, ![X14, X15, X16]:((r2_hidden(k1_mcart_1(X14),X15)|~r2_hidden(X14,k2_zfmisc_1(X15,X16)))&(r2_hidden(k2_mcart_1(X14),X16)|~r2_hidden(X14,k2_zfmisc_1(X15,X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.37  cnf(c_0_17, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))|v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_20, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X1!=k2_mcart_1(X1)|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (esk4_0=k1_mcart_1(esk4_0)|esk4_0=k2_mcart_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_22, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X1!=k1_mcart_1(X1)|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  fof(c_0_23, plain, ![X12, X13]:(~r2_hidden(X12,X13)|~r1_tarski(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.37  fof(c_0_24, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.37  fof(c_0_25, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_26, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.19/0.37  cnf(c_0_28, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|~m1_subset_1(esk4_0,k2_zfmisc_1(X2,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.19/0.37  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_32, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(k1_mcart_1(esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(k2_mcart_1(esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_14])).
% 0.19/0.37  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.37  cnf(c_0_39, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_39])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 41
% 0.19/0.37  # Proof object clause steps            : 23
% 0.19/0.37  # Proof object formula steps           : 18
% 0.19/0.37  # Proof object conjectures             : 15
% 0.19/0.37  # Proof object clause conjectures      : 12
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 9
% 0.19/0.37  # Proof object generating inferences   : 9
% 0.19/0.37  # Proof object simplifying inferences  : 6
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 9
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 14
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 14
% 0.19/0.37  # Processed clauses                    : 28
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 28
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 10
% 0.19/0.37  # Generated clauses                    : 27
% 0.19/0.37  # ...of the previous two non-trivial   : 25
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 27
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 18
% 0.19/0.37  #    Positive orientable unit clauses  : 4
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 12
% 0.19/0.37  # Current number of unprocessed clauses: 11
% 0.19/0.37  # ...number of literals in the above   : 22
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 10
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 14
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 13
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 11
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 2
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1027
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
