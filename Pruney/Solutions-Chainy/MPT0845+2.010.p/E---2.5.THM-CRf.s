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
% DateTime   : Thu Dec  3 10:58:55 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   39 (  81 expanded)
%              Number of clauses        :   23 (  38 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 271 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_mcart_1,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

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

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t1_mcart_1])).

fof(c_0_9,negated_conjecture,(
    ! [X33] :
      ( esk6_0 != k1_xboole_0
      & ( ~ r2_hidden(X33,esk6_0)
        | ~ r1_xboole_0(X33,esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X17] :
      ( ( r2_hidden(esk2_2(X14,X15),X15)
        | ~ r2_hidden(X14,X15) )
      & ( ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X17,esk2_2(X14,X15))
        | ~ r2_hidden(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_11,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_xboole_0(X8,X9) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r1_xboole_0(esk2_2(X1,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,esk2_2(X2,X3))
    | ~ r2_hidden(esk1_2(X1,esk2_2(X2,X3)),X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X18,X19,X20,X21,X23,X24,X25,X26,X28] :
      ( ( r2_hidden(k4_tarski(X21,esk3_4(X18,X19,X20,X21)),X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk3_4(X18,X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X18)
        | ~ r2_hidden(X24,X19)
        | r2_hidden(X23,X20)
        | X20 != k10_relat_1(X18,X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(esk4_3(X18,X25,X26),X26)
        | ~ r2_hidden(k4_tarski(esk4_3(X18,X25,X26),X28),X18)
        | ~ r2_hidden(X28,X25)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk4_3(X18,X25,X26),esk5_3(X18,X25,X26)),X18)
        | r2_hidden(esk4_3(X18,X25,X26),X26)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk5_3(X18,X25,X26),X25)
        | r2_hidden(esk4_3(X18,X25,X26),X26)
        | X26 = k10_relat_1(X18,X25)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r1_xboole_0(esk6_0,esk2_2(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,esk2_2(X2,X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X31] :
      ( v1_relat_1(k6_relat_1(X31))
      & v1_funct_1(k6_relat_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_28,plain,(
    ! [X30] : k10_relat_1(k1_xboole_0,X30) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

cnf(c_0_29,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_32]),c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.14/0.38  # and selection function SelectComplexExceptRRHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t1_mcart_1, conjecture, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.14/0.38  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.14/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.14/0.38  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.14/0.38  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.14/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.14/0.38  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 0.14/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1)))))), inference(assume_negation,[status(cth)],[t1_mcart_1])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ![X33]:(esk6_0!=k1_xboole_0&(~r2_hidden(X33,esk6_0)|~r1_xboole_0(X33,esk6_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X14, X15, X17]:((r2_hidden(esk2_2(X14,X15),X15)|~r2_hidden(X14,X15))&(~r2_hidden(X17,X15)|~r2_hidden(X17,esk2_2(X14,X15))|~r2_hidden(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X8, X9, X11, X12, X13]:(((r2_hidden(esk1_2(X8,X9),X8)|r1_xboole_0(X8,X9))&(r2_hidden(esk1_2(X8,X9),X9)|r1_xboole_0(X8,X9)))&(~r2_hidden(X13,X11)|~r2_hidden(X13,X12)|~r1_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r1_xboole_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_14, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.14/0.38  cnf(c_0_15, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r1_xboole_0(esk2_2(X1,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_18, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  cnf(c_0_19, plain, (r1_xboole_0(X1,esk2_2(X2,X3))|~r2_hidden(esk1_2(X1,esk2_2(X2,X3)),X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  fof(c_0_21, plain, ![X18, X19, X20, X21, X23, X24, X25, X26, X28]:((((r2_hidden(k4_tarski(X21,esk3_4(X18,X19,X20,X21)),X18)|~r2_hidden(X21,X20)|X20!=k10_relat_1(X18,X19)|~v1_relat_1(X18))&(r2_hidden(esk3_4(X18,X19,X20,X21),X19)|~r2_hidden(X21,X20)|X20!=k10_relat_1(X18,X19)|~v1_relat_1(X18)))&(~r2_hidden(k4_tarski(X23,X24),X18)|~r2_hidden(X24,X19)|r2_hidden(X23,X20)|X20!=k10_relat_1(X18,X19)|~v1_relat_1(X18)))&((~r2_hidden(esk4_3(X18,X25,X26),X26)|(~r2_hidden(k4_tarski(esk4_3(X18,X25,X26),X28),X18)|~r2_hidden(X28,X25))|X26=k10_relat_1(X18,X25)|~v1_relat_1(X18))&((r2_hidden(k4_tarski(esk4_3(X18,X25,X26),esk5_3(X18,X25,X26)),X18)|r2_hidden(esk4_3(X18,X25,X26),X26)|X26=k10_relat_1(X18,X25)|~v1_relat_1(X18))&(r2_hidden(esk5_3(X18,X25,X26),X25)|r2_hidden(esk4_3(X18,X25,X26),X26)|X26=k10_relat_1(X18,X25)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r1_xboole_0(esk6_0,esk2_2(X1,esk6_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  cnf(c_0_23, plain, (r1_xboole_0(X1,esk2_2(X2,X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.14/0.38  cnf(c_0_24, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  fof(c_0_25, plain, ![X31]:(v1_relat_1(k6_relat_1(X31))&v1_funct_1(k6_relat_1(X31))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_27, plain, (r2_hidden(esk3_4(X1,X2,k10_relat_1(X1,X2),X3),X2)|~v1_relat_1(X1)|~r2_hidden(X3,k10_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.14/0.38  fof(c_0_28, plain, ![X30]:k10_relat_1(k1_xboole_0,X30)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.14/0.38  cnf(c_0_29, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  cnf(c_0_32, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_33, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X1)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.14/0.38  cnf(c_0_36, plain, (X1=k1_xboole_0|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_32]), c_0_35])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_36]), c_0_37]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 39
% 0.14/0.38  # Proof object clause steps            : 23
% 0.14/0.38  # Proof object formula steps           : 16
% 0.14/0.38  # Proof object conjectures             : 11
% 0.14/0.38  # Proof object clause conjectures      : 8
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 12
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 10
% 0.14/0.38  # Proof object simplifying inferences  : 6
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 18
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 18
% 0.14/0.38  # Processed clauses                    : 117
% 0.14/0.38  # ...of these trivial                  : 5
% 0.14/0.38  # ...subsumed                          : 39
% 0.14/0.38  # ...remaining for further processing  : 73
% 0.14/0.38  # Other redundant clauses eliminated   : 3
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 7
% 0.14/0.38  # Generated clauses                    : 128
% 0.14/0.38  # ...of the previous two non-trivial   : 109
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 125
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 3
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 45
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 32
% 0.14/0.38  # Current number of unprocessed clauses: 28
% 0.14/0.38  # ...number of literals in the above   : 96
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 25
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 240
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 189
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 28
% 0.14/0.38  # Unit Clause-clause subsumption calls : 36
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 7
% 0.14/0.38  # BW rewrite match successes           : 7
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2675
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
