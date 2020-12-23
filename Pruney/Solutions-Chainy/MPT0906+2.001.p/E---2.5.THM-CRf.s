%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:05 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 (  66 expanded)
%              Number of clauses        :   22 (  30 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 190 expanded)
%              Number of equality atoms :   48 (  99 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t66_mcart_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) != k1_xboole_0
     => ! [X3] :
          ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
         => ( X3 != k1_mcart_1(X3)
            & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t26_mcart_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ! [X3] :
              ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
             => ( X3 != k1_mcart_1(X3)
                & X3 != k2_mcart_1(X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(fc4_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X6] :
      ( ( r1_xboole_0(X6,X6)
        | X6 != k1_xboole_0 )
      & ( X6 = k1_xboole_0
        | ~ r1_xboole_0(X6,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) != k1_xboole_0
       => ! [X3] :
            ( m1_subset_1(X3,k2_zfmisc_1(X1,X2))
           => ( X3 != k1_mcart_1(X3)
              & X3 != k2_mcart_1(X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t66_mcart_1])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( v1_xboole_0(X8)
      | ~ r1_tarski(X8,X7)
      | ~ r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] :
      ( ( X16 != k1_mcart_1(X16)
        | ~ m1_subset_1(X16,k2_zfmisc_1(X14,X15))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X16 != k2_mcart_1(X16)
        | ~ m1_subset_1(X16,k2_zfmisc_1(X14,X15))
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_mcart_1])])])])).

fof(c_0_15,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0
    & m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))
    & ( esk3_0 = k1_mcart_1(esk3_0)
      | esk3_0 = k2_mcart_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ~ v1_xboole_0(X11)
      | v1_xboole_0(k2_zfmisc_1(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 != k2_mcart_1(X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( esk3_0 = k1_mcart_1(esk3_0)
    | esk3_0 = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X1 != k1_mcart_1(X1)
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

fof(c_0_26,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(X12)
      | v1_xboole_0(k2_zfmisc_1(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ m1_subset_1(esk3_0,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_36]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00DA
% 0.12/0.35  # and selection function SelectSmallestOrientable.
% 0.12/0.35  #
% 0.12/0.35  # Preprocessing time       : 0.021 s
% 0.12/0.35  # Presaturation interreduction done
% 0.12/0.35  
% 0.12/0.35  # Proof found!
% 0.12/0.35  # SZS status Theorem
% 0.12/0.35  # SZS output start CNFRefutation
% 0.12/0.35  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.12/0.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.35  fof(t66_mcart_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)!=k1_xboole_0=>![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_mcart_1)).
% 0.12/0.35  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.12/0.35  fof(t26_mcart_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~(![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 0.12/0.35  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.12/0.35  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 0.12/0.35  fof(fc4_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 0.12/0.35  fof(c_0_8, plain, ![X6]:((r1_xboole_0(X6,X6)|X6!=k1_xboole_0)&(X6=k1_xboole_0|~r1_xboole_0(X6,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.12/0.35  fof(c_0_9, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.35  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)!=k1_xboole_0=>![X3]:(m1_subset_1(X3,k2_zfmisc_1(X1,X2))=>(X3!=k1_mcart_1(X3)&X3!=k2_mcart_1(X3))))), inference(assume_negation,[status(cth)],[t66_mcart_1])).
% 0.12/0.35  fof(c_0_11, plain, ![X7, X8]:(v1_xboole_0(X8)|(~r1_tarski(X8,X7)|~r1_xboole_0(X8,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.12/0.35  cnf(c_0_12, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.35  cnf(c_0_13, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.35  fof(c_0_14, plain, ![X14, X15, X16]:((X16!=k1_mcart_1(X16)|~m1_subset_1(X16,k2_zfmisc_1(X14,X15))|(X14=k1_xboole_0|X15=k1_xboole_0))&(X16!=k2_mcart_1(X16)|~m1_subset_1(X16,k2_zfmisc_1(X14,X15))|(X14=k1_xboole_0|X15=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_mcart_1])])])])).
% 0.12/0.35  fof(c_0_15, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0&(m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))&(esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.12/0.35  fof(c_0_16, plain, ![X10, X11]:(~v1_xboole_0(X11)|v1_xboole_0(k2_zfmisc_1(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.12/0.35  cnf(c_0_17, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.35  cnf(c_0_18, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_13])).
% 0.12/0.35  cnf(c_0_20, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X1!=k2_mcart_1(X1)|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.35  cnf(c_0_21, negated_conjecture, (esk3_0=k1_mcart_1(esk3_0)|esk3_0=k2_mcart_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_22, plain, (X2=k1_xboole_0|X3=k1_xboole_0|X1!=k1_mcart_1(X1)|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.35  fof(c_0_23, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.12/0.35  cnf(c_0_24, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.35  cnf(c_0_25, plain, (v1_xboole_0(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.12/0.35  fof(c_0_26, plain, ![X12, X13]:(~v1_xboole_0(X12)|v1_xboole_0(k2_zfmisc_1(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_zfmisc_1])])).
% 0.12/0.35  cnf(c_0_27, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|~m1_subset_1(esk3_0,k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.12/0.35  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.35  cnf(c_0_30, plain, (v1_xboole_0(k2_zfmisc_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.35  cnf(c_0_31, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.35  cnf(c_0_32, negated_conjecture, (k2_zfmisc_1(esk1_0,esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.35  cnf(c_0_33, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.35  cnf(c_0_34, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.35  cnf(c_0_35, plain, (v1_xboole_0(k2_zfmisc_1(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_31, c_0_25])).
% 0.12/0.35  cnf(c_0_36, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.12/0.35  cnf(c_0_37, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_35])).
% 0.12/0.35  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_36]), c_0_37])]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 39
% 0.12/0.35  # Proof object clause steps            : 22
% 0.12/0.35  # Proof object formula steps           : 17
% 0.12/0.35  # Proof object conjectures             : 10
% 0.12/0.35  # Proof object clause conjectures      : 7
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 11
% 0.12/0.35  # Proof object initial formulas used   : 8
% 0.12/0.35  # Proof object generating inferences   : 8
% 0.12/0.35  # Proof object simplifying inferences  : 10
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 8
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 14
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 14
% 0.12/0.35  # Processed clauses                    : 37
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 0
% 0.12/0.35  # ...remaining for further processing  : 37
% 0.12/0.35  # Other redundant clauses eliminated   : 3
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 0
% 0.12/0.35  # Backward-rewritten                   : 5
% 0.12/0.35  # Generated clauses                    : 17
% 0.12/0.35  # ...of the previous two non-trivial   : 15
% 0.12/0.35  # Contextual simplify-reflections      : 1
% 0.12/0.35  # Paramodulations                      : 14
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 3
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 16
% 0.12/0.35  #    Positive orientable unit clauses  : 6
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 0
% 0.12/0.35  #    Non-unit-clauses                  : 10
% 0.12/0.35  # Current number of unprocessed clauses: 5
% 0.12/0.35  # ...number of literals in the above   : 6
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 18
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 15
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 15
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.35  # Unit Clause-clause subsumption calls : 5
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 3
% 0.12/0.35  # BW rewrite match successes           : 3
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 1020
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.021 s
% 0.12/0.35  # System time              : 0.004 s
% 0.12/0.35  # Total time               : 0.026 s
% 0.12/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
