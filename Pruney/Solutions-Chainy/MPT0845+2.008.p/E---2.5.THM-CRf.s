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
% DateTime   : Thu Dec  3 10:58:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  83 expanded)
%              Number of clauses        :   20 (  37 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  107 ( 296 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t1_mcart_1,conjecture,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t150_relat_1,axiom,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(c_0_7,plain,(
    ! [X13,X14,X16] :
      ( ( r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,esk2_2(X13,X14))
        | ~ r2_hidden(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

fof(c_0_8,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ~ ( X1 != k1_xboole_0
          & ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r1_xboole_0(X2,X1) ) ) ),
    inference(assume_negation,[status(cth)],[t1_mcart_1])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,esk2_2(esk1_2(X1,X2),X2))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_13,negated_conjecture,(
    ! [X34] :
      ( esk6_0 != k1_xboole_0
      & ( ~ r2_hidden(X34,esk6_0)
        | ~ r1_xboole_0(X34,esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

cnf(c_0_14,plain,
    ( r1_xboole_0(X1,X2)
    | r1_xboole_0(X3,X2)
    | ~ r2_hidden(esk1_2(X1,X2),esk2_2(esk1_2(X3,X2),X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_17,plain,(
    ! [X30] :
      ( v1_relat_1(k6_relat_1(X30))
      & v1_funct_1(k6_relat_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_xboole_0(esk2_2(esk1_2(X1,X2),X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_2(esk1_2(X1,X2),X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_10])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( r2_hidden(k4_tarski(esk3_4(X17,X18,X19,X20),X20),X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk3_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X23,X22),X17)
        | ~ r2_hidden(X23,X18)
        | r2_hidden(X22,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(esk4_3(X17,X24,X25),X25)
        | ~ r2_hidden(k4_tarski(X27,esk4_3(X17,X24,X25)),X17)
        | ~ r2_hidden(X27,X24)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk5_3(X17,X24,X25),esk4_3(X17,X24,X25)),X17)
        | r2_hidden(esk4_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk5_3(X17,X24,X25),X24)
        | r2_hidden(esk4_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_22,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_24,plain,(
    ! [X29] : k9_relat_1(k1_xboole_0,X29) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t150_relat_1])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(X1,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_25])])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X2)
    | r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_3(k1_xboole_0,esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_31]),c_0_32]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.19/0.38  # and selection function SelectCQIArNpEqFirst.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 0.19/0.38  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.38  fof(t1_mcart_1, conjecture, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.19/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.38  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 0.19/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.38  fof(t150_relat_1, axiom, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 0.19/0.38  fof(c_0_7, plain, ![X13, X14, X16]:((r2_hidden(esk2_2(X13,X14),X14)|~r2_hidden(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,esk2_2(X13,X14))|~r2_hidden(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.19/0.38  fof(c_0_8, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.38  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1)))))), inference(assume_negation,[status(cth)],[t1_mcart_1])).
% 0.19/0.38  cnf(c_0_12, plain, (r1_xboole_0(X1,X2)|~r2_hidden(X3,esk2_2(esk1_2(X1,X2),X2))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ![X34]:(esk6_0!=k1_xboole_0&(~r2_hidden(X34,esk6_0)|~r1_xboole_0(X34,esk6_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.19/0.38  cnf(c_0_14, plain, (r1_xboole_0(X1,X2)|r1_xboole_0(X3,X2)|~r2_hidden(esk1_2(X1,X2),esk2_2(esk1_2(X3,X2),X2))), inference(spm,[status(thm)],[c_0_12, c_0_10])).
% 0.19/0.38  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_16, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  fof(c_0_17, plain, ![X30]:(v1_relat_1(k6_relat_1(X30))&v1_funct_1(k6_relat_1(X30))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (~r2_hidden(X1,esk6_0)|~r1_xboole_0(X1,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_19, plain, (r1_xboole_0(esk2_2(esk1_2(X1,X2),X2),X2)|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_20, plain, (r2_hidden(esk2_2(esk1_2(X1,X2),X2),X2)|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_10])).
% 0.19/0.38  fof(c_0_21, plain, ![X17, X18, X19, X20, X22, X23, X24, X25, X27]:((((r2_hidden(k4_tarski(esk3_4(X17,X18,X19,X20),X20),X17)|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|~v1_relat_1(X17))&(r2_hidden(esk3_4(X17,X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|~v1_relat_1(X17)))&(~r2_hidden(k4_tarski(X23,X22),X17)|~r2_hidden(X23,X18)|r2_hidden(X22,X19)|X19!=k9_relat_1(X17,X18)|~v1_relat_1(X17)))&((~r2_hidden(esk4_3(X17,X24,X25),X25)|(~r2_hidden(k4_tarski(X27,esk4_3(X17,X24,X25)),X17)|~r2_hidden(X27,X24))|X25=k9_relat_1(X17,X24)|~v1_relat_1(X17))&((r2_hidden(k4_tarski(esk5_3(X17,X24,X25),esk4_3(X17,X24,X25)),X17)|r2_hidden(esk4_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|~v1_relat_1(X17))&(r2_hidden(esk5_3(X17,X24,X25),X24)|r2_hidden(esk4_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|~v1_relat_1(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.19/0.38  cnf(c_0_22, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_23, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.38  fof(c_0_24, plain, ![X29]:k9_relat_1(k1_xboole_0,X29)=k1_xboole_0, inference(variable_rename,[status(thm)],[t150_relat_1])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r1_xboole_0(X1,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.19/0.38  cnf(c_0_26, plain, (r2_hidden(esk5_3(X1,X2,X3),X2)|r2_hidden(esk4_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_27, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.38  cnf(c_0_28, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_25])])).
% 0.19/0.38  cnf(c_0_30, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X2)|r2_hidden(esk4_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk4_3(k1_xboole_0,esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_31]), c_0_32]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 34
% 0.19/0.38  # Proof object clause steps            : 20
% 0.19/0.38  # Proof object formula steps           : 14
% 0.19/0.38  # Proof object conjectures             : 9
% 0.19/0.38  # Proof object clause conjectures      : 6
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 10
% 0.19/0.38  # Proof object initial formulas used   : 7
% 0.19/0.38  # Proof object generating inferences   : 9
% 0.19/0.38  # Proof object simplifying inferences  : 5
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 9
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 19
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 19
% 0.19/0.38  # Processed clauses                    : 96
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 15
% 0.19/0.38  # ...remaining for further processing  : 80
% 0.19/0.38  # Other redundant clauses eliminated   : 3
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 1
% 0.19/0.38  # Generated clauses                    : 132
% 0.19/0.38  # ...of the previous two non-trivial   : 115
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 129
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 3
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 57
% 0.19/0.38  #    Positive orientable unit clauses  : 11
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 4
% 0.19/0.38  #    Non-unit-clauses                  : 42
% 0.19/0.38  # Current number of unprocessed clauses: 57
% 0.19/0.38  # ...number of literals in the above   : 184
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 20
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 579
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 318
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.19/0.38  # Unit Clause-clause subsumption calls : 28
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3279
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.032 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
