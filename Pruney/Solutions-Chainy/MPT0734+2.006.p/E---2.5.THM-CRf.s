%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:10 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   38 (  62 expanded)
%              Number of clauses        :   21 (  24 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 228 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_ordinal1,conjecture,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r1_tarski(X1,X2)
                  & r2_hidden(X2,X3) )
               => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t21_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_xboole_0(X1,X2)
           => r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( v1_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ! [X3] :
                ( v3_ordinal1(X3)
               => ( ( r1_tarski(X1,X2)
                    & r2_hidden(X2,X3) )
                 => r2_hidden(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_ordinal1])).

fof(c_0_9,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & v3_ordinal1(esk4_0)
    & r1_tarski(esk2_0,esk3_0)
    & r2_hidden(esk3_0,esk4_0)
    & ~ r2_hidden(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X11] :
      ( ( v1_ordinal1(X11)
        | ~ v3_ordinal1(X11) )
      & ( v2_ordinal1(X11)
        | ~ v3_ordinal1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(k2_xboole_0(X6,X7),X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v1_ordinal1(X12)
        | ~ r2_hidden(X13,X12)
        | r1_tarski(X13,X12) )
      & ( r2_hidden(esk1_1(X14),X14)
        | v1_ordinal1(X14) )
      & ( ~ r1_tarski(esk1_1(X14),X14)
        | v1_ordinal1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_16,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v1_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | ~ r2_xboole_0(X4,X5) )
      & ( X4 != X5
        | ~ r2_xboole_0(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | X4 = X5
        | r2_xboole_0(X4,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ~ v1_ordinal1(X16)
      | ~ v3_ordinal1(X17)
      | ~ r2_xboole_0(X16,X17)
      | r2_hidden(X16,X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ~ r2_hidden(X18,X19)
      | ~ r1_tarski(X19,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = esk4_0
    | r2_xboole_0(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( v1_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_17])]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_35]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:16:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.11/0.36  # and selection function SelectNewComplexAHP.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.027 s
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(t22_ordinal1, conjecture, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r1_tarski(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 0.11/0.36  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.11/0.36  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.11/0.36  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.11/0.36  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.11/0.36  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.11/0.36  fof(t21_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_xboole_0(X1,X2)=>r2_hidden(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 0.11/0.36  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.11/0.36  fof(c_0_8, negated_conjecture, ~(![X1]:(v1_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>![X3]:(v3_ordinal1(X3)=>((r1_tarski(X1,X2)&r2_hidden(X2,X3))=>r2_hidden(X1,X3)))))), inference(assume_negation,[status(cth)],[t22_ordinal1])).
% 0.11/0.36  fof(c_0_9, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.11/0.36  fof(c_0_10, negated_conjecture, (v1_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&(v3_ordinal1(esk4_0)&((r1_tarski(esk2_0,esk3_0)&r2_hidden(esk3_0,esk4_0))&~r2_hidden(esk2_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.11/0.36  fof(c_0_11, plain, ![X11]:((v1_ordinal1(X11)|~v3_ordinal1(X11))&(v2_ordinal1(X11)|~v3_ordinal1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.11/0.36  fof(c_0_12, plain, ![X6, X7, X8]:(~r1_tarski(k2_xboole_0(X6,X7),X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.11/0.36  cnf(c_0_13, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.36  cnf(c_0_14, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  fof(c_0_15, plain, ![X12, X13, X14]:((~v1_ordinal1(X12)|(~r2_hidden(X13,X12)|r1_tarski(X13,X12)))&((r2_hidden(esk1_1(X14),X14)|v1_ordinal1(X14))&(~r1_tarski(esk1_1(X14),X14)|v1_ordinal1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.11/0.36  cnf(c_0_16, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_17, negated_conjecture, (v3_ordinal1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  cnf(c_0_18, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.36  cnf(c_0_19, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.11/0.36  cnf(c_0_20, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.11/0.36  cnf(c_0_21, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  cnf(c_0_22, negated_conjecture, (v1_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.36  fof(c_0_23, plain, ![X4, X5]:(((r1_tarski(X4,X5)|~r2_xboole_0(X4,X5))&(X4!=X5|~r2_xboole_0(X4,X5)))&(~r1_tarski(X4,X5)|X4=X5|r2_xboole_0(X4,X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.11/0.36  cnf(c_0_24, negated_conjecture, (r1_tarski(esk2_0,X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.36  cnf(c_0_25, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.11/0.36  fof(c_0_26, plain, ![X16, X17]:(~v1_ordinal1(X16)|(~v3_ordinal1(X17)|(~r2_xboole_0(X16,X17)|r2_hidden(X16,X17)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_ordinal1])])])).
% 0.11/0.36  cnf(c_0_27, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.36  cnf(c_0_28, negated_conjecture, (r1_tarski(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.11/0.36  fof(c_0_29, plain, ![X18, X19]:(~r2_hidden(X18,X19)|~r1_tarski(X19,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.11/0.36  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~v1_ordinal1(X1)|~v3_ordinal1(X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.36  cnf(c_0_31, negated_conjecture, (esk2_0=esk4_0|r2_xboole_0(esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.11/0.36  cnf(c_0_32, negated_conjecture, (v1_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.36  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.11/0.36  cnf(c_0_35, negated_conjecture, (esk2_0=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_17])]), c_0_33])).
% 0.11/0.36  cnf(c_0_36, negated_conjecture, (~r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.11/0.36  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_14, c_0_35]), c_0_36]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 38
% 0.11/0.36  # Proof object clause steps            : 21
% 0.11/0.36  # Proof object formula steps           : 17
% 0.11/0.36  # Proof object conjectures             : 17
% 0.11/0.36  # Proof object clause conjectures      : 14
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 12
% 0.11/0.36  # Proof object initial formulas used   : 8
% 0.11/0.36  # Proof object generating inferences   : 8
% 0.11/0.36  # Proof object simplifying inferences  : 8
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 8
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 18
% 0.11/0.36  # Removed in clause preprocessing      : 0
% 0.11/0.36  # Initial clauses in saturation        : 18
% 0.11/0.36  # Processed clauses                    : 35
% 0.11/0.36  # ...of these trivial                  : 0
% 0.11/0.36  # ...subsumed                          : 0
% 0.11/0.36  # ...remaining for further processing  : 35
% 0.11/0.36  # Other redundant clauses eliminated   : 1
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 11
% 0.11/0.36  # Generated clauses                    : 25
% 0.11/0.36  # ...of the previous two non-trivial   : 27
% 0.11/0.36  # Contextual simplify-reflections      : 0
% 0.11/0.36  # Paramodulations                      : 24
% 0.11/0.36  # Factorizations                       : 0
% 0.11/0.36  # Equation resolutions                 : 1
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 23
% 0.11/0.36  #    Positive orientable unit clauses  : 8
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 2
% 0.11/0.36  #    Non-unit-clauses                  : 13
% 0.11/0.36  # Current number of unprocessed clauses: 2
% 0.11/0.36  # ...number of literals in the above   : 4
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 11
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 11
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 9
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.11/0.36  # Unit Clause-clause subsumption calls : 10
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 1
% 0.11/0.36  # BW rewrite match successes           : 1
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 1120
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.026 s
% 0.11/0.36  # System time              : 0.005 s
% 0.11/0.36  # Total time               : 0.031 s
% 0.11/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
