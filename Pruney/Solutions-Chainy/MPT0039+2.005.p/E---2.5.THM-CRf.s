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
% DateTime   : Thu Dec  3 10:32:01 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 235 expanded)
%              Number of clauses        :   39 ( 121 expanded)
%              Number of leaves         :    3 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  120 (1364 expanded)
%              Number of equality atoms :   47 ( 454 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_xboole_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t32_xboole_1])).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k4_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k4_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k4_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_5,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0)
    & esk3_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | X2 != k4_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])).

cnf(c_0_14,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_11])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( k4_xboole_0(X1,esk4_0) = X1
    | r2_hidden(esk1_3(X1,esk4_0,X1),esk3_0)
    | X2 != k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( X1 != k4_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_8]),c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_11])).

cnf(c_0_21,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( k4_xboole_0(X1,esk4_0) = X1
    | r2_hidden(esk1_3(X1,esk4_0,X1),esk3_0) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_6])).

cnf(c_0_25,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk4_0,X2)) = k4_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_31,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(esk2_2(X14,X15),X14)
        | ~ r2_hidden(esk2_2(X14,X15),X15)
        | X14 = X15 )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r2_hidden(esk2_2(X14,X15),X15)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_32,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk4_0,X1),esk3_0) = k4_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | X2 != k4_xboole_0(esk3_0,esk4_0)
    | ~ r2_hidden(X1,k4_xboole_0(esk4_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_32]),c_0_9])).

cnf(c_0_36,plain,
    ( X1 = X2
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X2,X3))
    | r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k4_xboole_0(esk4_0,X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk3_0,esk4_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( X1 = esk3_0
    | r2_hidden(esk2_2(X1,esk3_0),esk4_0)
    | r2_hidden(esk2_2(X1,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_39]),c_0_40])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r2_hidden(esk2_2(X1,X2),X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:36:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.70/0.90  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.70/0.90  # and selection function SelectNewComplexAHP.
% 0.70/0.90  #
% 0.70/0.90  # Preprocessing time       : 0.033 s
% 0.70/0.90  
% 0.70/0.90  # Proof found!
% 0.70/0.90  # SZS status Theorem
% 0.70/0.90  # SZS output start CNFRefutation
% 0.70/0.90  fof(t32_xboole_1, conjecture, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.70/0.90  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.70/0.90  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.70/0.90  fof(c_0_3, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t32_xboole_1])).
% 0.70/0.90  fof(c_0_4, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6))&(~r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k4_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k4_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k4_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k4_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.70/0.90  fof(c_0_5, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)&esk3_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.70/0.90  cnf(c_0_6, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.70/0.90  cnf(c_0_7, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.70/0.90  cnf(c_0_8, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.70/0.90  cnf(c_0_9, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.70/0.90  cnf(c_0_10, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.70/0.90  cnf(c_0_11, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X1)), inference(ef,[status(thm)],[c_0_6])).
% 0.70/0.90  cnf(c_0_12, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.70/0.90  cnf(c_0_13, negated_conjecture, (r2_hidden(X1,esk3_0)|X2!=k4_xboole_0(esk3_0,esk4_0)|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])).
% 0.70/0.90  cnf(c_0_14, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk1_3(X1,X2,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_11])).
% 0.70/0.90  cnf(c_0_15, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_12])).
% 0.70/0.90  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_9])).
% 0.70/0.90  cnf(c_0_17, negated_conjecture, (k4_xboole_0(X1,esk4_0)=X1|r2_hidden(esk1_3(X1,esk4_0,X1),esk3_0)|X2!=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.70/0.90  cnf(c_0_18, negated_conjecture, (X1!=k4_xboole_0(esk3_0,esk4_0)|~r2_hidden(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_8]), c_0_12])).
% 0.70/0.90  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.70/0.90  cnf(c_0_20, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|~r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_15, c_0_11])).
% 0.70/0.90  cnf(c_0_21, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.70/0.90  cnf(c_0_22, negated_conjecture, (k4_xboole_0(X1,esk4_0)=X1|r2_hidden(esk1_3(X1,esk4_0,X1),esk3_0)), inference(er,[status(thm)],[c_0_17])).
% 0.70/0.90  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk3_0,esk4_0))), inference(er,[status(thm)],[c_0_18])).
% 0.70/0.90  cnf(c_0_24, plain, (X1=k4_xboole_0(X2,X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_6])).
% 0.70/0.90  cnf(c_0_25, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X3))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.70/0.90  cnf(c_0_26, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),esk4_0)=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_22])).
% 0.70/0.90  cnf(c_0_27, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k4_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.70/0.90  cnf(c_0_28, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X2,X3),X4))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_25])).
% 0.70/0.90  cnf(c_0_29, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,esk3_0),k4_xboole_0(esk4_0,X2))=k4_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.70/0.90  cnf(c_0_30, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.70/0.90  fof(c_0_31, plain, ![X14, X15]:((~r2_hidden(esk2_2(X14,X15),X14)|~r2_hidden(esk2_2(X14,X15),X15)|X14=X15)&(r2_hidden(esk2_2(X14,X15),X14)|r2_hidden(esk2_2(X14,X15),X15)|X14=X15)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.70/0.90  cnf(c_0_32, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk4_0,X1),esk3_0)=k4_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.70/0.90  cnf(c_0_33, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_7])).
% 0.70/0.90  cnf(c_0_34, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.70/0.90  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,esk3_0)|X2!=k4_xboole_0(esk3_0,esk4_0)|~r2_hidden(X1,k4_xboole_0(esk4_0,X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_32]), c_0_9])).
% 0.70/0.90  cnf(c_0_36, plain, (X1=X2|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X2,X3))|r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X3)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.70/0.90  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k4_xboole_0(esk4_0,X2))), inference(er,[status(thm)],[c_0_35])).
% 0.70/0.90  cnf(c_0_38, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk3_0,esk4_0))=X1), inference(spm,[status(thm)],[c_0_23, c_0_14])).
% 0.70/0.90  cnf(c_0_39, negated_conjecture, (X1=esk3_0|r2_hidden(esk2_2(X1,esk3_0),esk4_0)|r2_hidden(esk2_2(X1,esk3_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_36])).
% 0.70/0.90  cnf(c_0_40, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.70/0.90  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.70/0.90  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_39]), c_0_40])).
% 0.70/0.90  cnf(c_0_43, plain, (X1=X2|~r2_hidden(esk2_2(X1,X2),X1)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.70/0.90  cnf(c_0_44, negated_conjecture, (r2_hidden(esk2_2(esk4_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.70/0.90  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_42])]), c_0_40]), ['proof']).
% 0.70/0.90  # SZS output end CNFRefutation
% 0.70/0.90  # Proof object total steps             : 46
% 0.70/0.90  # Proof object clause steps            : 39
% 0.70/0.90  # Proof object formula steps           : 7
% 0.70/0.90  # Proof object conjectures             : 23
% 0.70/0.90  # Proof object clause conjectures      : 20
% 0.70/0.90  # Proof object formula conjectures     : 3
% 0.70/0.90  # Proof object initial clauses used    : 10
% 0.70/0.90  # Proof object initial formulas used   : 3
% 0.70/0.90  # Proof object generating inferences   : 29
% 0.70/0.90  # Proof object simplifying inferences  : 8
% 0.70/0.90  # Training examples: 0 positive, 0 negative
% 0.70/0.90  # Parsed axioms                        : 3
% 0.70/0.90  # Removed by relevancy pruning/SinE    : 0
% 0.70/0.90  # Initial clauses                      : 10
% 0.70/0.90  # Removed in clause preprocessing      : 0
% 0.70/0.90  # Initial clauses in saturation        : 10
% 0.70/0.90  # Processed clauses                    : 9721
% 0.70/0.90  # ...of these trivial                  : 491
% 0.70/0.90  # ...subsumed                          : 8591
% 0.70/0.90  # ...remaining for further processing  : 639
% 0.70/0.90  # Other redundant clauses eliminated   : 70
% 0.70/0.90  # Clauses deleted for lack of memory   : 0
% 0.70/0.90  # Backward-subsumed                    : 69
% 0.70/0.90  # Backward-rewritten                   : 4
% 0.70/0.90  # Generated clauses                    : 63949
% 0.70/0.90  # ...of the previous two non-trivial   : 48706
% 0.70/0.90  # Contextual simplify-reflections      : 8
% 0.70/0.90  # Paramodulations                      : 63613
% 0.70/0.90  # Factorizations                       : 86
% 0.70/0.90  # Equation resolutions                 : 241
% 0.70/0.90  # Propositional unsat checks           : 0
% 0.70/0.90  #    Propositional check models        : 0
% 0.70/0.90  #    Propositional check unsatisfiable : 0
% 0.70/0.90  #    Propositional clauses             : 0
% 0.70/0.90  #    Propositional clauses after purity: 0
% 0.70/0.90  #    Propositional unsat core size     : 0
% 0.70/0.90  #    Propositional preprocessing time  : 0.000
% 0.70/0.90  #    Propositional encoding time       : 0.000
% 0.70/0.90  #    Propositional solver time         : 0.000
% 0.70/0.90  #    Success case prop preproc time    : 0.000
% 0.70/0.90  #    Success case prop encoding time   : 0.000
% 0.70/0.90  #    Success case prop solver time     : 0.000
% 0.70/0.90  # Current number of processed clauses  : 566
% 0.70/0.90  #    Positive orientable unit clauses  : 92
% 0.70/0.90  #    Positive unorientable unit clauses: 2
% 0.70/0.90  #    Negative unit clauses             : 5
% 0.70/0.90  #    Non-unit-clauses                  : 467
% 0.70/0.90  # Current number of unprocessed clauses: 38693
% 0.70/0.90  # ...number of literals in the above   : 108586
% 0.70/0.90  # Current number of archived formulas  : 0
% 0.70/0.90  # Current number of archived clauses   : 73
% 0.70/0.90  # Clause-clause subsumption calls (NU) : 85511
% 0.70/0.90  # Rec. Clause-clause subsumption calls : 60448
% 0.70/0.90  # Non-unit clause-clause subsumptions  : 6264
% 0.70/0.90  # Unit Clause-clause subsumption calls : 1033
% 0.70/0.90  # Rewrite failures with RHS unbound    : 41
% 0.70/0.90  # BW rewrite match attempts            : 659
% 0.70/0.90  # BW rewrite match successes           : 10
% 0.70/0.90  # Condensation attempts                : 0
% 0.70/0.90  # Condensation successes               : 0
% 0.70/0.90  # Termbank termtop insertions          : 864942
% 0.70/0.90  
% 0.70/0.90  # -------------------------------------------------
% 0.70/0.90  # User time                : 0.523 s
% 0.70/0.90  # System time              : 0.027 s
% 0.70/0.90  # Total time               : 0.550 s
% 0.70/0.90  # Maximum resident set size: 1556 pages
%------------------------------------------------------------------------------
