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
% DateTime   : Thu Dec  3 10:45:55 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 214 expanded)
%              Number of clauses        :   35 ( 105 expanded)
%              Number of leaves         :   10 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  141 ( 565 expanded)
%              Number of equality atoms :   45 ( 196 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t38_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( r1_tarski(X2,k3_subset_1(X1,X2))
      <=> X2 = k1_subset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d3_subset_1,axiom,(
    ! [X1] : k1_subset_1(X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X22,X23] : k4_xboole_0(X22,X23) = k5_xboole_0(X22,k3_xboole_0(X22,X23)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_12,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X34,X33)
        | r1_tarski(X34,X32)
        | X33 != k1_zfmisc_1(X32) )
      & ( ~ r1_tarski(X35,X32)
        | r2_hidden(X35,X33)
        | X33 != k1_zfmisc_1(X32) )
      & ( ~ r2_hidden(esk3_2(X36,X37),X37)
        | ~ r1_tarski(esk3_2(X36,X37),X36)
        | X37 = k1_zfmisc_1(X36) )
      & ( r2_hidden(esk3_2(X36,X37),X37)
        | r1_tarski(esk3_2(X36,X37),X36)
        | X37 = k1_zfmisc_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_13,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ( r1_tarski(X2,k3_subset_1(X1,X2))
        <=> X2 = k1_subset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t38_subset_1])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X29,X30] : r1_tarski(k4_xboole_0(X29,X30),X29) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))
    & ( ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
      | esk5_0 != k1_subset_1(esk4_0) )
    & ( r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
      | esk5_0 = k1_subset_1(esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_21,plain,(
    ! [X41] : k1_subset_1(X41) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[d3_subset_1])).

cnf(c_0_22,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X31] :
      ( ~ r1_tarski(X31,k1_xboole_0)
      | X31 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_26,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
    | esk5_0 != k1_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_subset_1(X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
    | esk5_0 = k1_subset_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_36,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(esk4_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

fof(c_0_43,plain,(
    ! [X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | k3_subset_1(X42,X43) = k4_xboole_0(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_42])])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_46,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k1_xboole_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk5_0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X1,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0)) = k3_subset_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k3_subset_1(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk5_0,k1_xboole_0),k3_subset_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_47]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 0.13/0.41  # and selection function SelectCQIArEqFirst.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.028 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.41  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.41  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.13/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.41  fof(t38_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 0.13/0.42  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.13/0.42  fof(d3_subset_1, axiom, ![X1]:k1_subset_1(X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 0.13/0.42  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.13/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.42  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.13/0.42  fof(c_0_10, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.42  fof(c_0_11, plain, ![X22, X23]:k4_xboole_0(X22,X23)=k5_xboole_0(X22,k3_xboole_0(X22,X23)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.42  fof(c_0_12, plain, ![X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X34,X33)|r1_tarski(X34,X32)|X33!=k1_zfmisc_1(X32))&(~r1_tarski(X35,X32)|r2_hidden(X35,X33)|X33!=k1_zfmisc_1(X32)))&((~r2_hidden(esk3_2(X36,X37),X37)|~r1_tarski(esk3_2(X36,X37),X36)|X37=k1_zfmisc_1(X36))&(r2_hidden(esk3_2(X36,X37),X37)|r1_tarski(esk3_2(X36,X37),X36)|X37=k1_zfmisc_1(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.13/0.42  fof(c_0_13, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.42  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(r1_tarski(X2,k3_subset_1(X1,X2))<=>X2=k1_subset_1(X1)))), inference(assume_negation,[status(cth)],[t38_subset_1])).
% 0.13/0.42  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.42  cnf(c_0_16, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.42  cnf(c_0_17, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.42  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.42  fof(c_0_19, plain, ![X29, X30]:r1_tarski(k4_xboole_0(X29,X30),X29), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.13/0.42  fof(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))&((~r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0!=k1_subset_1(esk4_0))&(r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0=k1_subset_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.42  fof(c_0_21, plain, ![X41]:k1_subset_1(X41)=k1_xboole_0, inference(variable_rename,[status(thm)],[d3_subset_1])).
% 0.13/0.42  cnf(c_0_22, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.42  cnf(c_0_23, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.42  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.13/0.42  fof(c_0_25, plain, ![X31]:(~r1_tarski(X31,k1_xboole_0)|X31=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.13/0.42  cnf(c_0_26, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.42  cnf(c_0_27, negated_conjecture, (~r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0!=k1_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.42  cnf(c_0_28, plain, (k1_subset_1(X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.42  cnf(c_0_29, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|esk5_0=k1_subset_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.42  cnf(c_0_30, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.42  cnf(c_0_31, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.42  cnf(c_0_32, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.42  cnf(c_0_33, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_26, c_0_16])).
% 0.13/0.42  cnf(c_0_34, negated_conjecture, (esk5_0!=k1_xboole_0|~r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.42  cnf(c_0_35, negated_conjecture, (esk5_0=k1_xboole_0|r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.13/0.42  fof(c_0_36, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.42  cnf(c_0_37, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1))))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.42  cnf(c_0_38, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.42  cnf(c_0_39, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))|~r1_tarski(k1_xboole_0,k3_subset_1(esk4_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.42  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.42  cnf(c_0_41, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.42  cnf(c_0_42, negated_conjecture, (r1_tarski(esk5_0,k3_subset_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.13/0.42  fof(c_0_43, plain, ![X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(X42))|k3_subset_1(X42,X43)=k4_xboole_0(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.13/0.42  cnf(c_0_44, negated_conjecture, (esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_42])])).
% 0.13/0.42  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 0.13/0.42  cnf(c_0_46, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.42  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k1_xboole_0),esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.42  cnf(c_0_48, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_46, c_0_16])).
% 0.13/0.42  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.42  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.13/0.42  cnf(c_0_51, negated_conjecture, (~r2_hidden(esk1_2(esk5_0,k1_xboole_0),k5_xboole_0(X1,k3_xboole_0(X1,esk5_0)))), inference(spm,[status(thm)],[c_0_30, c_0_47])).
% 0.13/0.42  cnf(c_0_52, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,esk5_0))=k3_subset_1(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.42  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,k3_subset_1(esk4_0,esk5_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 0.13/0.42  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk1_2(esk5_0,k1_xboole_0),k3_subset_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.42  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_47]), c_0_54]), ['proof']).
% 0.13/0.42  # SZS output end CNFRefutation
% 0.13/0.42  # Proof object total steps             : 56
% 0.13/0.42  # Proof object clause steps            : 35
% 0.13/0.42  # Proof object formula steps           : 21
% 0.13/0.42  # Proof object conjectures             : 17
% 0.13/0.42  # Proof object clause conjectures      : 14
% 0.13/0.42  # Proof object formula conjectures     : 3
% 0.13/0.42  # Proof object initial clauses used    : 13
% 0.13/0.42  # Proof object initial formulas used   : 10
% 0.13/0.42  # Proof object generating inferences   : 13
% 0.13/0.42  # Proof object simplifying inferences  : 12
% 0.13/0.42  # Training examples: 0 positive, 0 negative
% 0.13/0.42  # Parsed axioms                        : 14
% 0.13/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.42  # Initial clauses                      : 31
% 0.13/0.42  # Removed in clause preprocessing      : 2
% 0.13/0.42  # Initial clauses in saturation        : 29
% 0.13/0.42  # Processed clauses                    : 436
% 0.13/0.42  # ...of these trivial                  : 35
% 0.13/0.42  # ...subsumed                          : 131
% 0.13/0.42  # ...remaining for further processing  : 269
% 0.13/0.42  # Other redundant clauses eliminated   : 7
% 0.13/0.42  # Clauses deleted for lack of memory   : 0
% 0.13/0.42  # Backward-subsumed                    : 2
% 0.13/0.42  # Backward-rewritten                   : 35
% 0.13/0.42  # Generated clauses                    : 2690
% 0.13/0.42  # ...of the previous two non-trivial   : 2126
% 0.13/0.42  # Contextual simplify-reflections      : 0
% 0.13/0.42  # Paramodulations                      : 2683
% 0.13/0.42  # Factorizations                       : 0
% 0.13/0.42  # Equation resolutions                 : 7
% 0.13/0.42  # Propositional unsat checks           : 0
% 0.13/0.42  #    Propositional check models        : 0
% 0.13/0.42  #    Propositional check unsatisfiable : 0
% 0.13/0.42  #    Propositional clauses             : 0
% 0.13/0.42  #    Propositional clauses after purity: 0
% 0.13/0.42  #    Propositional unsat core size     : 0
% 0.13/0.42  #    Propositional preprocessing time  : 0.000
% 0.13/0.42  #    Propositional encoding time       : 0.000
% 0.13/0.42  #    Propositional solver time         : 0.000
% 0.13/0.42  #    Success case prop preproc time    : 0.000
% 0.13/0.42  #    Success case prop encoding time   : 0.000
% 0.13/0.42  #    Success case prop solver time     : 0.000
% 0.13/0.42  # Current number of processed clauses  : 197
% 0.13/0.42  #    Positive orientable unit clauses  : 71
% 0.13/0.42  #    Positive unorientable unit clauses: 0
% 0.13/0.42  #    Negative unit clauses             : 43
% 0.13/0.42  #    Non-unit-clauses                  : 83
% 0.13/0.42  # Current number of unprocessed clauses: 1663
% 0.13/0.42  # ...number of literals in the above   : 4165
% 0.13/0.42  # Current number of archived formulas  : 0
% 0.13/0.42  # Current number of archived clauses   : 67
% 0.13/0.42  # Clause-clause subsumption calls (NU) : 1064
% 0.13/0.42  # Rec. Clause-clause subsumption calls : 927
% 0.13/0.42  # Non-unit clause-clause subsumptions  : 65
% 0.13/0.42  # Unit Clause-clause subsumption calls : 452
% 0.13/0.42  # Rewrite failures with RHS unbound    : 0
% 0.13/0.42  # BW rewrite match attempts            : 49
% 0.13/0.42  # BW rewrite match successes           : 16
% 0.13/0.42  # Condensation attempts                : 0
% 0.13/0.42  # Condensation successes               : 0
% 0.13/0.42  # Termbank termtop insertions          : 30948
% 0.13/0.42  
% 0.13/0.42  # -------------------------------------------------
% 0.13/0.42  # User time                : 0.068 s
% 0.13/0.42  # System time              : 0.005 s
% 0.13/0.42  # Total time               : 0.072 s
% 0.13/0.42  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
