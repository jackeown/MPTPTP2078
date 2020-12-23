%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 304 expanded)
%              Number of clauses        :   34 ( 125 expanded)
%              Number of leaves         :    7 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 (1590 expanded)
%              Number of equality atoms :   17 (  75 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_relat_1(X30)
      | k1_relat_1(k5_relat_1(X29,X30)) = k10_relat_1(X29,k1_relat_1(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & ( ~ r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0)))
      | ~ r2_hidden(esk6_0,k1_relat_1(esk8_0))
      | ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0)) )
    & ( r2_hidden(esk6_0,k1_relat_1(esk8_0))
      | r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0))) )
    & ( r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))
      | r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(k10_relat_1(X28,X27),k1_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk8_0,X1)) = k10_relat_1(esk8_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( ~ r2_hidden(X13,X12)
        | r2_hidden(k4_tarski(esk2_3(X11,X12,X13),X13),X11)
        | X12 != k2_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(X16,X15),X11)
        | r2_hidden(X15,X12)
        | X12 != k2_relat_1(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(k4_tarski(X20,esk3_2(X17,X18)),X17)
        | X18 = k2_relat_1(X17) )
      & ( r2_hidden(esk3_2(X17,X18),X18)
        | r2_hidden(k4_tarski(esk4_2(X17,X18),esk3_2(X17,X18)),X17)
        | X18 = k2_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_17,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(X31,k1_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( X32 = k1_funct_1(X33,X31)
        | ~ r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(X31,k1_relat_1(X33))
        | X32 != k1_funct_1(X33,X31)
        | r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk8_0))
    | r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk8_0,esk7_0)) = k10_relat_1(esk8_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X26] :
      ( ( r2_hidden(esk5_3(X22,X23,X24),k2_relat_1(X24))
        | ~ r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(X22,esk5_3(X22,X23,X24)),X24)
        | ~ r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk5_3(X22,X23,X24),X23)
        | ~ r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X26,k2_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X26),X24)
        | ~ r2_hidden(X26,X23)
        | r2_hidden(X22,k10_relat_1(X24,X23))
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_23,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))
    | r2_hidden(esk6_0,k1_relat_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_11])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk8_0,esk6_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_11])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))
    | r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk6_0,k10_relat_1(esk8_0,X1))
    | ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_11])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))
    | r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0)))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk8_0))
    | ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,esk5_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))
    | ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_21])).

cnf(c_0_41,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_3(esk6_0,k1_relat_1(esk7_0),esk8_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_11])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))
    | ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_30])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_3(esk6_0,k1_relat_1(esk7_0),esk8_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_39]),c_0_11])])).

cnf(c_0_46,negated_conjecture,
    ( esk5_3(esk6_0,k1_relat_1(esk7_0),esk8_0) = k1_funct_1(esk8_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_31]),c_0_11])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t21_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 0.20/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.20/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.38  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t21_funct_1])).
% 0.20/0.38  fof(c_0_8, plain, ![X29, X30]:(~v1_relat_1(X29)|(~v1_relat_1(X30)|k1_relat_1(k5_relat_1(X29,X30))=k10_relat_1(X29,k1_relat_1(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&((~r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0)))|(~r2_hidden(esk6_0,k1_relat_1(esk8_0))|~r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))))&((r2_hidden(esk6_0,k1_relat_1(esk8_0))|r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0))))&(r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))|r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.20/0.38  cnf(c_0_10, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_12, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  fof(c_0_13, plain, ![X27, X28]:(~v1_relat_1(X28)|r1_tarski(k10_relat_1(X28,X27),k1_relat_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (k1_relat_1(k5_relat_1(esk8_0,X1))=k10_relat_1(esk8_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_16, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:(((~r2_hidden(X13,X12)|r2_hidden(k4_tarski(esk2_3(X11,X12,X13),X13),X11)|X12!=k2_relat_1(X11))&(~r2_hidden(k4_tarski(X16,X15),X11)|r2_hidden(X15,X12)|X12!=k2_relat_1(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|~r2_hidden(k4_tarski(X20,esk3_2(X17,X18)),X17)|X18=k2_relat_1(X17))&(r2_hidden(esk3_2(X17,X18),X18)|r2_hidden(k4_tarski(esk4_2(X17,X18),esk3_2(X17,X18)),X17)|X18=k2_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.38  fof(c_0_17, plain, ![X31, X32, X33]:(((r2_hidden(X31,k1_relat_1(X33))|~r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(X32=k1_funct_1(X33,X31)|~r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(~r2_hidden(X31,k1_relat_1(X33))|X32!=k1_funct_1(X33,X31)|r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_19, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk8_0))|r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (k1_relat_1(k5_relat_1(esk8_0,esk7_0))=k10_relat_1(esk8_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  fof(c_0_22, plain, ![X22, X23, X24, X26]:((((r2_hidden(esk5_3(X22,X23,X24),k2_relat_1(X24))|~r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24))&(r2_hidden(k4_tarski(X22,esk5_3(X22,X23,X24)),X24)|~r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24)))&(r2_hidden(esk5_3(X22,X23,X24),X23)|~r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24)))&(~r2_hidden(X26,k2_relat_1(X24))|~r2_hidden(k4_tarski(X22,X26),X24)|~r2_hidden(X26,X23)|r2_hidden(X22,k10_relat_1(X24,X23))|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k10_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))|r2_hidden(esk6_0,k1_relat_1(esk8_0))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_27, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_28, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.38  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_11])])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_32, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,k1_funct_1(esk8_0,esk6_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_11])])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))|r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk6_0,k10_relat_1(esk8_0,X1))|~r2_hidden(k1_funct_1(esk8_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_11])])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))|r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))), inference(rw,[status(thm)],[c_0_34, c_0_21])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(k5_relat_1(esk8_0,esk7_0)))|~r2_hidden(esk6_0,k1_relat_1(esk8_0))|~r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,esk5_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))|~r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))|~r2_hidden(esk6_0,k1_relat_1(esk8_0))), inference(rw,[status(thm)],[c_0_37, c_0_21])).
% 0.20/0.38  cnf(c_0_41, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.38  cnf(c_0_42, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk5_3(esk6_0,k1_relat_1(esk7_0),esk8_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_11])])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (~r2_hidden(esk6_0,k10_relat_1(esk8_0,k1_relat_1(esk7_0)))|~r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_30])])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_3(esk6_0,k1_relat_1(esk7_0),esk8_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_39]), c_0_11])])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (esk5_3(esk6_0,k1_relat_1(esk7_0),esk8_0)=k1_funct_1(esk8_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_31]), c_0_11])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (~r2_hidden(k1_funct_1(esk8_0,esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_39])])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 49
% 0.20/0.38  # Proof object clause steps            : 34
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 24
% 0.20/0.38  # Proof object clause conjectures      : 21
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 10
% 0.20/0.38  # Proof object simplifying inferences  : 26
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 23
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 23
% 0.20/0.38  # Processed clauses                    : 79
% 0.20/0.38  # ...of these trivial                  : 3
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 76
% 0.20/0.38  # Other redundant clauses eliminated   : 3
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 10
% 0.20/0.38  # Generated clauses                    : 76
% 0.20/0.38  # ...of the previous two non-trivial   : 75
% 0.20/0.38  # Contextual simplify-reflections      : 1
% 0.20/0.38  # Paramodulations                      : 73
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 3
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 40
% 0.20/0.38  #    Positive orientable unit clauses  : 14
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 25
% 0.20/0.38  # Current number of unprocessed clauses: 39
% 0.20/0.38  # ...number of literals in the above   : 105
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 33
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 130
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 63
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 2
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 4
% 0.20/0.38  # BW rewrite match successes           : 4
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3316
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.006 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
