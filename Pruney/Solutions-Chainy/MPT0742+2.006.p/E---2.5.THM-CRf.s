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
% DateTime   : Thu Dec  3 10:56:14 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 195 expanded)
%              Number of clauses        :   29 (  79 expanded)
%              Number of leaves         :    9 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  148 ( 924 expanded)
%              Number of equality atoms :    8 (  65 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_ordinal1,conjecture,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ~ ( r1_tarski(X1,X2)
          & X1 != k1_xboole_0
          & ! [X3] :
              ( v3_ordinal1(X3)
             => ~ ( r2_hidden(X3,X1)
                  & ! [X4] :
                      ( v3_ordinal1(X4)
                     => ( r2_hidden(X4,X1)
                       => r1_ordinal1(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t7_tarski,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ! [X4] :
                  ~ ( r2_hidden(X4,X2)
                    & r2_hidden(X4,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t31_ordinal1,axiom,(
    ! [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
         => ( v3_ordinal1(X2)
            & r1_tarski(X2,X1) ) )
     => v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

fof(t24_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ~ ( ~ r2_hidden(X1,X2)
              & X1 != X2
              & ~ r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v3_ordinal1(X2)
       => ~ ( r1_tarski(X1,X2)
            & X1 != k1_xboole_0
            & ! [X3] :
                ( v3_ordinal1(X3)
               => ~ ( r2_hidden(X3,X1)
                    & ! [X4] :
                        ( v3_ordinal1(X4)
                       => ( r2_hidden(X4,X1)
                         => r1_ordinal1(X3,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_ordinal1])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X28] :
      ( v3_ordinal1(esk5_0)
      & r1_tarski(esk4_0,esk5_0)
      & esk4_0 != k1_xboole_0
      & ( v3_ordinal1(esk6_1(X28))
        | ~ r2_hidden(X28,esk4_0)
        | ~ v3_ordinal1(X28) )
      & ( r2_hidden(esk6_1(X28),esk4_0)
        | ~ r2_hidden(X28,esk4_0)
        | ~ v3_ordinal1(X28) )
      & ( ~ r1_ordinal1(X28,esk6_1(X28))
        | ~ r2_hidden(X28,esk4_0)
        | ~ v3_ordinal1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X16,X17] :
      ( ~ v3_ordinal1(X17)
      | ~ r2_hidden(X16,X17)
      | v3_ordinal1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_ordinal1(X1,esk6_1(X1))
    | ~ r2_hidden(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ~ v3_ordinal1(X20)
      | ~ v3_ordinal1(X21)
      | r1_ordinal1(X20,X21)
      | r2_hidden(X21,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_ordinal1(X1,esk6_1(X1))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X12,X13,X15] :
      ( ( r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,esk2_2(X12,X13))
        | ~ r2_hidden(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_1(X1),X1)
    | ~ v3_ordinal1(esk6_1(X1))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk6_1(X1))
    | ~ r2_hidden(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_26,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X24,X25)
      | ~ r1_tarski(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_27,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk2_2(X3,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_1(X1),X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_19])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X22] :
      ( ( r2_hidden(esk3_1(X22),X22)
        | v3_ordinal1(X22) )
      & ( ~ v3_ordinal1(esk3_1(X22))
        | ~ r1_tarski(esk3_1(X22),X22)
        | v3_ordinal1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_ordinal1])])])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk6_1(esk2_2(X1,X2)),X2)
    | ~ r2_hidden(esk2_2(X1,X2),esk4_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_1(X1),esk4_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X18,X19] :
      ( ~ v3_ordinal1(X18)
      | ~ v3_ordinal1(X19)
      | r2_hidden(X18,X19)
      | X18 = X19
      | r2_hidden(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ v3_ordinal1(esk2_2(X1,esk4_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( v3_ordinal1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_19]),c_0_35])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_xboole_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v3_ordinal1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:03:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t32_ordinal1, conjecture, ![X1, X2]:(v3_ordinal1(X2)=>~(((r1_tarski(X1,X2)&X1!=k1_xboole_0)&![X3]:(v3_ordinal1(X3)=>~((r2_hidden(X3,X1)&![X4]:(v3_ordinal1(X4)=>(r2_hidden(X4,X1)=>r1_ordinal1(X3,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_ordinal1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.12/0.37  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.12/0.37  fof(t7_tarski, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&![X3]:~((r2_hidden(X3,X2)&![X4]:~((r2_hidden(X4,X2)&r2_hidden(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 0.12/0.37  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.12/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.37  fof(t31_ordinal1, axiom, ![X1]:(![X2]:(r2_hidden(X2,X1)=>(v3_ordinal1(X2)&r1_tarski(X2,X1)))=>v3_ordinal1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_ordinal1)).
% 0.12/0.37  fof(t24_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>~(((~(r2_hidden(X1,X2))&X1!=X2)&~(r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2]:(v3_ordinal1(X2)=>~(((r1_tarski(X1,X2)&X1!=k1_xboole_0)&![X3]:(v3_ordinal1(X3)=>~((r2_hidden(X3,X1)&![X4]:(v3_ordinal1(X4)=>(r2_hidden(X4,X1)=>r1_ordinal1(X3,X4)))))))))), inference(assume_negation,[status(cth)],[t32_ordinal1])).
% 0.12/0.37  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, ![X28]:(v3_ordinal1(esk5_0)&((r1_tarski(esk4_0,esk5_0)&esk4_0!=k1_xboole_0)&((v3_ordinal1(esk6_1(X28))|~r2_hidden(X28,esk4_0)|~v3_ordinal1(X28))&((r2_hidden(esk6_1(X28),esk4_0)|~r2_hidden(X28,esk4_0)|~v3_ordinal1(X28))&(~r1_ordinal1(X28,esk6_1(X28))|~r2_hidden(X28,esk4_0)|~v3_ordinal1(X28)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X16, X17]:(~v3_ordinal1(X17)|(~r2_hidden(X16,X17)|v3_ordinal1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.12/0.37  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_15, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (~r1_ordinal1(X1,esk6_1(X1))|~r2_hidden(X1,esk4_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v3_ordinal1(X1)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.12/0.37  fof(c_0_20, plain, ![X20, X21]:(~v3_ordinal1(X20)|(~v3_ordinal1(X21)|(r1_ordinal1(X20,X21)|r2_hidden(X21,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (~r1_ordinal1(X1,esk6_1(X1))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_22, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  fof(c_0_23, plain, ![X12, X13, X15]:((r2_hidden(esk2_2(X12,X13),X13)|~r2_hidden(X12,X13))&(~r2_hidden(X15,X13)|~r2_hidden(X15,esk2_2(X12,X13))|~r2_hidden(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tarski])])])])])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk6_1(X1),X1)|~v3_ordinal1(esk6_1(X1))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_19])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk6_1(X1))|~r2_hidden(X1,esk4_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_26, plain, ![X24, X25]:(~r2_hidden(X24,X25)|~r1_tarski(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.12/0.37  fof(c_0_27, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.37  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,esk2_2(X3,X2))|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (r2_hidden(esk6_1(X1),X1)|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_19])).
% 0.12/0.37  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  fof(c_0_32, plain, ![X22]:((r2_hidden(esk3_1(X22),X22)|v3_ordinal1(X22))&(~v3_ordinal1(esk3_1(X22))|~r1_tarski(esk3_1(X22),X22)|v3_ordinal1(X22))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_ordinal1])])])])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk6_1(esk2_2(X1,X2)),X2)|~r2_hidden(esk2_2(X1,X2),esk4_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk6_1(X1),esk4_0)|~r2_hidden(X1,esk4_0)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  fof(c_0_36, plain, ![X18, X19]:(~v3_ordinal1(X18)|(~v3_ordinal1(X19)|(r2_hidden(X18,X19)|X18=X19|r2_hidden(X19,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_ordinal1])])])])).
% 0.12/0.37  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.37  cnf(c_0_38, plain, (r2_hidden(esk3_1(X1),X1)|v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (~v3_ordinal1(esk2_2(X1,esk4_0))|~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.12/0.37  cnf(c_0_40, plain, (r2_hidden(X1,X2)|X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_41, plain, (v3_ordinal1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (~r2_hidden(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_19]), c_0_35])).
% 0.12/0.37  cnf(c_0_43, plain, (X1=k1_xboole_0|r2_hidden(k1_xboole_0,X1)|~v3_ordinal1(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_37])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (v3_ordinal1(esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (~r2_hidden(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_29])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 48
% 0.12/0.37  # Proof object clause steps            : 29
% 0.12/0.37  # Proof object formula steps           : 19
% 0.12/0.37  # Proof object conjectures             : 20
% 0.12/0.37  # Proof object clause conjectures      : 17
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 15
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 13
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 9
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 18
% 0.12/0.37  # Processed clauses                    : 64
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 13
% 0.12/0.37  # ...remaining for further processing  : 51
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 2
% 0.12/0.37  # Generated clauses                    : 77
% 0.12/0.37  # ...of the previous two non-trivial   : 66
% 0.12/0.37  # Contextual simplify-reflections      : 6
% 0.12/0.37  # Paramodulations                      : 77
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 47
% 0.12/0.37  #    Positive orientable unit clauses  : 6
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 6
% 0.12/0.37  #    Non-unit-clauses                  : 35
% 0.12/0.37  # Current number of unprocessed clauses: 17
% 0.12/0.37  # ...number of literals in the above   : 71
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 4
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 147
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 106
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.37  # Unit Clause-clause subsumption calls : 44
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2368
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.028 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.034 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
