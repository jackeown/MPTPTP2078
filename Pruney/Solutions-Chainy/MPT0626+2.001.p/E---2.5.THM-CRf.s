%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:15 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 330 expanded)
%              Number of clauses        :   33 ( 133 expanded)
%              Number of leaves         :    4 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 (1966 expanded)
%              Number of equality atoms :   21 ( 141 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
            <=> ( r2_hidden(X1,k1_relat_1(X3))
                & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_funct_1])).

fof(c_0_5,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k1_relat_1(k5_relat_1(X18,X19)) = k10_relat_1(X18,k1_relat_1(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & ( ~ r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0)))
      | ~ r2_hidden(esk4_0,k1_relat_1(esk6_0))
      | ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0)) )
    & ( r2_hidden(esk4_0,k1_relat_1(esk6_0))
      | r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0))) )
    & ( r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))
      | r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( r2_hidden(k4_tarski(X9,esk1_4(X6,X7,X8,X9)),X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X12),X6)
        | ~ r2_hidden(X12,X7)
        | r2_hidden(X11,X8)
        | X8 != k10_relat_1(X6,X7)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X13,X14),X14)
        | ~ r2_hidden(k4_tarski(esk2_3(X6,X13,X14),X16),X6)
        | ~ r2_hidden(X16,X13)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk2_3(X6,X13,X14),esk3_3(X6,X13,X14)),X6)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk3_3(X6,X13,X14),X13)
        | r2_hidden(esk2_3(X6,X13,X14),X14)
        | X14 = k10_relat_1(X6,X13)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_10,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk6_0,X1)) = k10_relat_1(esk6_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk6_0))
    | r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk6_0,esk5_0)) = k10_relat_1(esk6_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,k1_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X21 = k1_funct_1(X22,X20)
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X20,k1_relat_1(X22))
        | X21 != k1_funct_1(X22,X20)
        | r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))
    | r2_hidden(esk4_0,k1_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0)),esk6_0)
    | r2_hidden(esk4_0,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_8])])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_8])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk6_0,esk4_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_8])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))
    | r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,k10_relat_1(esk6_0,X1))
    | ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_8])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))
    | r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0)))
    | ~ r2_hidden(esk4_0,k1_relat_1(esk6_0))
    | ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))
    | ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))
    | ~ r2_hidden(esk4_0,k1_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_32]),c_0_8])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))
    | ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_24])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_8])])).

cnf(c_0_39,negated_conjecture,
    ( esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0) = k1_funct_1(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_21]),c_0_8])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:22:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.12/0.39  # and selection function SelectNewComplexAHP.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.041 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t21_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 0.12/0.39  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.12/0.39  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.12/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.12/0.39  fof(c_0_4, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t21_funct_1])).
% 0.12/0.39  fof(c_0_5, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k1_relat_1(k5_relat_1(X18,X19))=k10_relat_1(X18,k1_relat_1(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.12/0.39  fof(c_0_6, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((~r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0)))|(~r2_hidden(esk4_0,k1_relat_1(esk6_0))|~r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))))&((r2_hidden(esk4_0,k1_relat_1(esk6_0))|r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0))))&(r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))|r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.12/0.39  cnf(c_0_7, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.39  cnf(c_0_8, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  fof(c_0_9, plain, ![X6, X7, X8, X9, X11, X12, X13, X14, X16]:((((r2_hidden(k4_tarski(X9,esk1_4(X6,X7,X8,X9)),X6)|~r2_hidden(X9,X8)|X8!=k10_relat_1(X6,X7)|~v1_relat_1(X6))&(r2_hidden(esk1_4(X6,X7,X8,X9),X7)|~r2_hidden(X9,X8)|X8!=k10_relat_1(X6,X7)|~v1_relat_1(X6)))&(~r2_hidden(k4_tarski(X11,X12),X6)|~r2_hidden(X12,X7)|r2_hidden(X11,X8)|X8!=k10_relat_1(X6,X7)|~v1_relat_1(X6)))&((~r2_hidden(esk2_3(X6,X13,X14),X14)|(~r2_hidden(k4_tarski(esk2_3(X6,X13,X14),X16),X6)|~r2_hidden(X16,X13))|X14=k10_relat_1(X6,X13)|~v1_relat_1(X6))&((r2_hidden(k4_tarski(esk2_3(X6,X13,X14),esk3_3(X6,X13,X14)),X6)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k10_relat_1(X6,X13)|~v1_relat_1(X6))&(r2_hidden(esk3_3(X6,X13,X14),X13)|r2_hidden(esk2_3(X6,X13,X14),X14)|X14=k10_relat_1(X6,X13)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.12/0.39  cnf(c_0_10, negated_conjecture, (k1_relat_1(k5_relat_1(esk6_0,X1))=k10_relat_1(esk6_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.12/0.39  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,esk1_4(X2,X3,X4,X1)),X2)|~r2_hidden(X1,X4)|X4!=k10_relat_1(X2,X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_13, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk6_0))|r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_14, negated_conjecture, (k1_relat_1(k5_relat_1(esk6_0,esk5_0))=k10_relat_1(esk6_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.39  fof(c_0_15, plain, ![X20, X21, X22]:(((r2_hidden(X20,k1_relat_1(X22))|~r2_hidden(k4_tarski(X20,X21),X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(X21=k1_funct_1(X22,X20)|~r2_hidden(k4_tarski(X20,X21),X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X20,k1_relat_1(X22))|X21!=k1_funct_1(X22,X20)|r2_hidden(k4_tarski(X20,X21),X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.12/0.39  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,esk1_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)|~r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_17, negated_conjecture, (r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))|r2_hidden(esk4_0,k1_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.39  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_19, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0)),esk6_0)|r2_hidden(esk4_0,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_8])])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_22, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_8])])).
% 0.12/0.39  cnf(c_0_25, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk6_0,esk4_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21]), c_0_8])])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))|r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_0,k10_relat_1(esk6_0,X1))|~r2_hidden(k1_funct_1(esk6_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_8])])).
% 0.12/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))|r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))), inference(rw,[status(thm)],[c_0_27, c_0_14])).
% 0.12/0.39  cnf(c_0_30, negated_conjecture, (~r2_hidden(esk4_0,k1_relat_1(k5_relat_1(esk6_0,esk5_0)))|~r2_hidden(esk4_0,k1_relat_1(esk6_0))|~r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.39  cnf(c_0_31, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))|~r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))|~r2_hidden(esk4_0,k1_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_30, c_0_14])).
% 0.12/0.39  cnf(c_0_34, plain, (r2_hidden(esk1_4(X1,X2,k10_relat_1(X1,X2),X3),X2)|~r2_hidden(X3,k10_relat_1(X1,X2))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_31])).
% 0.12/0.39  cnf(c_0_35, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_32]), c_0_8])])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk4_0,k10_relat_1(esk6_0,k1_relat_1(esk5_0)))|~r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_24])])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_8])])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (esk1_4(esk6_0,k1_relat_1(esk5_0),k10_relat_1(esk6_0,k1_relat_1(esk5_0)),esk4_0)=k1_funct_1(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_21]), c_0_8])])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (~r2_hidden(k1_funct_1(esk6_0,esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_32])])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_40]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 42
% 0.12/0.39  # Proof object clause steps            : 33
% 0.12/0.39  # Proof object formula steps           : 9
% 0.12/0.39  # Proof object conjectures             : 25
% 0.12/0.39  # Proof object clause conjectures      : 22
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 13
% 0.12/0.39  # Proof object initial formulas used   : 4
% 0.12/0.39  # Proof object generating inferences   : 10
% 0.12/0.39  # Proof object simplifying inferences  : 30
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 4
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 17
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 17
% 0.12/0.39  # Processed clauses                    : 71
% 0.12/0.39  # ...of these trivial                  : 3
% 0.12/0.39  # ...subsumed                          : 1
% 0.12/0.39  # ...remaining for further processing  : 67
% 0.12/0.39  # Other redundant clauses eliminated   : 4
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 0
% 0.12/0.39  # Backward-rewritten                   : 13
% 0.12/0.39  # Generated clauses                    : 52
% 0.12/0.39  # ...of the previous two non-trivial   : 54
% 0.12/0.39  # Contextual simplify-reflections      : 0
% 0.12/0.39  # Paramodulations                      : 48
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 4
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 33
% 0.12/0.39  #    Positive orientable unit clauses  : 12
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 1
% 0.12/0.39  #    Non-unit-clauses                  : 20
% 0.12/0.39  # Current number of unprocessed clauses: 14
% 0.12/0.39  # ...number of literals in the above   : 47
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 30
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 74
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 24
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.39  # Unit Clause-clause subsumption calls : 6
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 4
% 0.12/0.39  # BW rewrite match successes           : 4
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 2677
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.043 s
% 0.12/0.39  # System time              : 0.008 s
% 0.12/0.39  # Total time               : 0.051 s
% 0.12/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
