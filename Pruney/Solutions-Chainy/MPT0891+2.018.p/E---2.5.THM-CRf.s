%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:55 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 218 expanded)
%              Number of clauses        :   37 (  91 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 807 expanded)
%              Number of equality atoms :  105 ( 654 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t51_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(t20_mcart_1,axiom,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(c_0_9,plain,(
    ! [X18,X19] : k2_xboole_0(k1_tarski(X18),X19) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_10,plain,(
    ! [X8] : k2_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_11,plain,(
    ! [X44,X45,X46,X47] :
      ( X44 = k1_xboole_0
      | X45 = k1_xboole_0
      | X46 = k1_xboole_0
      | ~ m1_subset_1(X47,k3_zfmisc_1(X44,X45,X46))
      | X47 = k3_mcart_1(k5_mcart_1(X44,X45,X46,X47),k6_mcart_1(X44,X45,X46,X47),k7_mcart_1(X44,X45,X46,X47)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_12,plain,(
    ! [X20,X21,X22] : k3_mcart_1(X20,X21,X22) = k4_tarski(k4_tarski(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                  & X4 != k6_mcart_1(X1,X2,X3,X4)
                  & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_mcart_1])).

fof(c_0_14,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X9
        | X10 != k1_tarski(X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k1_tarski(X9) )
      & ( ~ r2_hidden(esk1_2(X13,X14),X14)
        | esk1_2(X13,X14) != X13
        | X14 = k1_tarski(X13) )
      & ( r2_hidden(esk1_2(X13,X14),X14)
        | esk1_2(X13,X14) = X13
        | X14 = k1_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_15,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X39,X41,X42,X43] :
      ( ( r2_hidden(esk5_1(X39),X39)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X41,X39)
        | esk5_1(X39) != k3_mcart_1(X41,X42,X43)
        | X39 = k1_xboole_0 )
      & ( ~ r2_hidden(X42,X39)
        | esk5_1(X39) != k3_mcart_1(X41,X42,X43)
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    & esk7_0 != k1_xboole_0
    & esk8_0 != k1_xboole_0
    & m1_subset_1(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))
    & ( esk9_0 = k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)
      | esk9_0 = k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)
      | esk9_0 = k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_21,plain,(
    ! [X30,X31,X32] :
      ( ( X30 != k1_mcart_1(X30)
        | X30 != k4_tarski(X31,X32) )
      & ( X30 != k2_mcart_1(X30)
        | X30 != k4_tarski(X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).

cnf(c_0_22,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X48,X49] :
      ( k1_mcart_1(k4_tarski(X48,X49)) = X48
      & k2_mcart_1(k4_tarski(X48,X49)) = X49 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_26,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( X1 != k2_mcart_1(X1)
    | X1 != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk5_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(esk5_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)),k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)) = esk9_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) != k4_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk5_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,plain,
    ( X2 = k1_xboole_0
    | esk5_1(X2) != k4_tarski(k4_tarski(X3,X1),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_19])).

cnf(c_0_40,plain,
    ( esk5_1(k1_tarski(X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) = k2_mcart_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( k4_tarski(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_43,plain,
    ( X2 = k1_xboole_0
    | esk5_1(X2) != k4_tarski(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_19])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X2,X1),X3))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23])])).

cnf(c_0_45,negated_conjecture,
    ( k4_tarski(k4_tarski(k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)),k2_mcart_1(esk9_0)) = esk9_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( esk9_0 = k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)
    | esk9_0 = k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)
    | esk9_0 = k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) != esk9_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_36])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_23])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) = esk9_0
    | k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) = esk9_0 ),
    inference(sr,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0) = esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:44:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.18/0.37  # and selection function SelectNegativeLiterals.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.028 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.18/0.37  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.18/0.37  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.18/0.37  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.18/0.37  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.18/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.37  fof(t29_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k3_mcart_1(X3,X4,X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 0.18/0.37  fof(t20_mcart_1, axiom, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.18/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.18/0.37  fof(c_0_9, plain, ![X18, X19]:k2_xboole_0(k1_tarski(X18),X19)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.18/0.37  fof(c_0_10, plain, ![X8]:k2_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.18/0.37  fof(c_0_11, plain, ![X44, X45, X46, X47]:(X44=k1_xboole_0|X45=k1_xboole_0|X46=k1_xboole_0|(~m1_subset_1(X47,k3_zfmisc_1(X44,X45,X46))|X47=k3_mcart_1(k5_mcart_1(X44,X45,X46,X47),k6_mcart_1(X44,X45,X46,X47),k7_mcart_1(X44,X45,X46,X47)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.18/0.37  fof(c_0_12, plain, ![X20, X21, X22]:k3_mcart_1(X20,X21,X22)=k4_tarski(k4_tarski(X20,X21),X22), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.18/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.18/0.37  fof(c_0_14, plain, ![X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X11,X10)|X11=X9|X10!=k1_tarski(X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k1_tarski(X9)))&((~r2_hidden(esk1_2(X13,X14),X14)|esk1_2(X13,X14)!=X13|X14=k1_tarski(X13))&(r2_hidden(esk1_2(X13,X14),X14)|esk1_2(X13,X14)=X13|X14=k1_tarski(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.37  cnf(c_0_15, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_16, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.37  fof(c_0_17, plain, ![X39, X41, X42, X43]:((r2_hidden(esk5_1(X39),X39)|X39=k1_xboole_0)&((~r2_hidden(X41,X39)|esk5_1(X39)!=k3_mcart_1(X41,X42,X43)|X39=k1_xboole_0)&(~r2_hidden(X42,X39)|esk5_1(X39)!=k3_mcart_1(X41,X42,X43)|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).
% 0.18/0.37  cnf(c_0_18, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.37  cnf(c_0_19, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  fof(c_0_20, negated_conjecture, (((esk6_0!=k1_xboole_0&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&(m1_subset_1(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))&(esk9_0=k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)|esk9_0=k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)|esk9_0=k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.18/0.37  fof(c_0_21, plain, ![X30, X31, X32]:((X30!=k1_mcart_1(X30)|X30!=k4_tarski(X31,X32))&(X30!=k2_mcart_1(X30)|X30!=k4_tarski(X31,X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_mcart_1])])])])).
% 0.18/0.37  cnf(c_0_22, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_23, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.37  cnf(c_0_24, plain, (r2_hidden(esk5_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.37  fof(c_0_25, plain, ![X48, X49]:(k1_mcart_1(k4_tarski(X48,X49))=X48&k2_mcart_1(k4_tarski(X48,X49))=X49), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.18/0.37  cnf(c_0_26, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk9_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_28, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_29, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_31, plain, (X1!=k2_mcart_1(X1)|X1!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_32, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk5_1(X2)!=k3_mcart_1(X3,X1,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.37  cnf(c_0_33, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_22])).
% 0.18/0.37  cnf(c_0_34, plain, (r2_hidden(esk5_1(k1_tarski(X1)),k1_tarski(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.37  cnf(c_0_35, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)),k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0))=esk9_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.18/0.37  cnf(c_0_37, plain, (k2_mcart_1(k4_tarski(X1,X2))!=k4_tarski(X1,X2)), inference(er,[status(thm)],[c_0_31])).
% 0.18/0.37  cnf(c_0_38, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk5_1(X2)!=k3_mcart_1(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.37  cnf(c_0_39, plain, (X2=k1_xboole_0|esk5_1(X2)!=k4_tarski(k4_tarski(X3,X1),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_19])).
% 0.18/0.37  cnf(c_0_40, plain, (esk5_1(k1_tarski(X1))=X1), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)=k2_mcart_1(esk9_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.18/0.37  cnf(c_0_42, plain, (k4_tarski(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_37, c_0_35])).
% 0.18/0.37  cnf(c_0_43, plain, (X2=k1_xboole_0|esk5_1(X2)!=k4_tarski(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_19])).
% 0.18/0.37  cnf(c_0_44, plain, (~r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X2,X1),X3)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_23])])).
% 0.18/0.37  cnf(c_0_45, negated_conjecture, (k4_tarski(k4_tarski(k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)),k2_mcart_1(esk9_0))=esk9_0), inference(rw,[status(thm)],[c_0_36, c_0_41])).
% 0.18/0.37  cnf(c_0_46, negated_conjecture, (esk9_0=k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)|esk9_0=k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)|esk9_0=k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_47, negated_conjecture, (k7_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)!=esk9_0), inference(spm,[status(thm)],[c_0_42, c_0_36])).
% 0.18/0.37  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.37  cnf(c_0_49, plain, (~r2_hidden(X1,k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_40]), c_0_23])])).
% 0.18/0.37  cnf(c_0_50, negated_conjecture, (~r2_hidden(k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk9_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.37  cnf(c_0_51, negated_conjecture, (k6_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)=esk9_0|k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)=esk9_0), inference(sr,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.37  cnf(c_0_52, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.18/0.37  cnf(c_0_53, negated_conjecture, (~r2_hidden(k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0),k1_tarski(esk9_0))), inference(spm,[status(thm)],[c_0_49, c_0_45])).
% 0.18/0.37  cnf(c_0_54, negated_conjecture, (k5_mcart_1(esk6_0,esk7_0,esk8_0,esk9_0)=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.18/0.37  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_52])]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 56
% 0.18/0.37  # Proof object clause steps            : 37
% 0.18/0.37  # Proof object formula steps           : 19
% 0.18/0.37  # Proof object conjectures             : 17
% 0.18/0.37  # Proof object clause conjectures      : 14
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 16
% 0.18/0.37  # Proof object initial formulas used   : 9
% 0.18/0.37  # Proof object generating inferences   : 11
% 0.18/0.37  # Proof object simplifying inferences  : 22
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 12
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 28
% 0.18/0.37  # Removed in clause preprocessing      : 1
% 0.18/0.37  # Initial clauses in saturation        : 27
% 0.18/0.37  # Processed clauses                    : 166
% 0.18/0.37  # ...of these trivial                  : 7
% 0.18/0.37  # ...subsumed                          : 37
% 0.18/0.37  # ...remaining for further processing  : 122
% 0.18/0.37  # Other redundant clauses eliminated   : 60
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 2
% 0.18/0.37  # Backward-rewritten                   : 8
% 0.18/0.37  # Generated clauses                    : 987
% 0.18/0.37  # ...of the previous two non-trivial   : 572
% 0.18/0.37  # Contextual simplify-reflections      : 0
% 0.18/0.37  # Paramodulations                      : 924
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 63
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 80
% 0.18/0.37  #    Positive orientable unit clauses  : 20
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 12
% 0.18/0.37  #    Non-unit-clauses                  : 48
% 0.18/0.37  # Current number of unprocessed clauses: 442
% 0.18/0.37  # ...number of literals in the above   : 1403
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 39
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 223
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 192
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 33
% 0.18/0.37  # Unit Clause-clause subsumption calls : 90
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 7
% 0.18/0.37  # BW rewrite match successes           : 5
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 13348
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.040 s
% 0.18/0.37  # System time              : 0.004 s
% 0.18/0.37  # Total time               : 0.044 s
% 0.18/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
