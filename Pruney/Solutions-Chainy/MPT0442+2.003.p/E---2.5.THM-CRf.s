%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:14 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   37 (  56 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 195 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
                & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_relat_1])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_relat_1(esk7_0)
    & r1_tarski(esk6_0,esk7_0)
    & ( ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))
      | ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( ~ r2_hidden(X34,X33)
        | r2_hidden(k4_tarski(esk3_3(X32,X33,X34),X34),X32)
        | X33 != k2_relat_1(X32) )
      & ( ~ r2_hidden(k4_tarski(X37,X36),X32)
        | r2_hidden(X36,X33)
        | X33 != k2_relat_1(X32) )
      & ( ~ r2_hidden(esk4_2(X38,X39),X39)
        | ~ r2_hidden(k4_tarski(X41,esk4_2(X38,X39)),X38)
        | X39 = k2_relat_1(X38) )
      & ( r2_hidden(esk4_2(X38,X39),X39)
        | r2_hidden(k4_tarski(esk5_2(X38,X39),esk4_2(X38,X39)),X38)
        | X39 = k2_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_12,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | ~ v1_relat_1(X44)
      | k1_relat_1(k2_xboole_0(X43,X44)) = k2_xboole_0(k1_relat_1(X43),k1_relat_1(X44)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk6_0,X1,X2),X2),esk7_0)
    | X1 != k2_relat_1(esk6_0)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k2_xboole_0(X1,esk7_0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk7_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_21,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k2_xboole_0(X25,X26) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk7_0)
    | X3 != k2_relat_1(esk6_0)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k2_xboole_0(esk6_0,esk7_0)) = k2_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk7_0))
    | X2 != k2_relat_1(esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k2_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_10])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))
    | ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk7_0))
    | r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  # Version: 2.5pre002
% 0.21/0.34  # No SInE strategy applied
% 0.21/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.79  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.62/0.79  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.62/0.79  #
% 0.62/0.79  # Preprocessing time       : 0.028 s
% 0.62/0.79  # Presaturation interreduction done
% 0.62/0.79  
% 0.62/0.79  # Proof found!
% 0.62/0.79  # SZS status Theorem
% 0.62/0.79  # SZS output start CNFRefutation
% 0.62/0.79  fof(t25_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.62/0.79  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.62/0.79  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.62/0.79  fof(t13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 0.62/0.79  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.62/0.79  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.62/0.79  fof(c_0_6, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t25_relat_1])).
% 0.62/0.79  fof(c_0_7, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.62/0.79  fof(c_0_8, negated_conjecture, (v1_relat_1(esk6_0)&(v1_relat_1(esk7_0)&(r1_tarski(esk6_0,esk7_0)&(~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.62/0.79  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.62/0.79  cnf(c_0_10, negated_conjecture, (r1_tarski(esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  fof(c_0_11, plain, ![X32, X33, X34, X36, X37, X38, X39, X41]:(((~r2_hidden(X34,X33)|r2_hidden(k4_tarski(esk3_3(X32,X33,X34),X34),X32)|X33!=k2_relat_1(X32))&(~r2_hidden(k4_tarski(X37,X36),X32)|r2_hidden(X36,X33)|X33!=k2_relat_1(X32)))&((~r2_hidden(esk4_2(X38,X39),X39)|~r2_hidden(k4_tarski(X41,esk4_2(X38,X39)),X38)|X39=k2_relat_1(X38))&(r2_hidden(esk4_2(X38,X39),X39)|r2_hidden(k4_tarski(esk5_2(X38,X39),esk4_2(X38,X39)),X38)|X39=k2_relat_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.62/0.79  fof(c_0_12, plain, ![X43, X44]:(~v1_relat_1(X43)|(~v1_relat_1(X44)|k1_relat_1(k2_xboole_0(X43,X44))=k2_xboole_0(k1_relat_1(X43),k1_relat_1(X44)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relat_1])])])).
% 0.62/0.79  cnf(c_0_13, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.62/0.79  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.79  cnf(c_0_15, plain, (k1_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.62/0.79  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_17, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.62/0.79  cnf(c_0_18, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk6_0,X1,X2),X2),esk7_0)|X1!=k2_relat_1(esk6_0)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.62/0.79  cnf(c_0_19, negated_conjecture, (k1_relat_1(k2_xboole_0(X1,esk7_0))=k2_xboole_0(k1_relat_1(X1),k1_relat_1(esk7_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.62/0.79  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  fof(c_0_21, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k2_xboole_0(X25,X26)=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.62/0.79  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,X2)|X2!=k2_relat_1(esk7_0)|X3!=k2_relat_1(esk6_0)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.62/0.79  fof(c_0_23, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.62/0.79  cnf(c_0_24, negated_conjecture, (k1_relat_1(k2_xboole_0(esk6_0,esk7_0))=k2_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.62/0.79  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.79  cnf(c_0_26, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk7_0))|X2!=k2_relat_1(esk6_0)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_22])).
% 0.62/0.79  cnf(c_0_27, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.62/0.79  cnf(c_0_28, negated_conjecture, (k2_xboole_0(k1_relat_1(esk6_0),k1_relat_1(esk7_0))=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_10])])).
% 0.62/0.79  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(er,[status(thm)],[c_0_26])).
% 0.62/0.79  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.62/0.79  cnf(c_0_31, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))|~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.62/0.79  cnf(c_0_32, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.62/0.79  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.62/0.79  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk7_0))|r1_tarski(k2_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.62/0.79  cnf(c_0_35, negated_conjecture, (~r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])])).
% 0.62/0.79  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 0.62/0.79  # SZS output end CNFRefutation
% 0.62/0.79  # Proof object total steps             : 37
% 0.62/0.79  # Proof object clause steps            : 24
% 0.62/0.79  # Proof object formula steps           : 13
% 0.62/0.79  # Proof object conjectures             : 19
% 0.62/0.79  # Proof object clause conjectures      : 16
% 0.62/0.79  # Proof object formula conjectures     : 3
% 0.62/0.79  # Proof object initial clauses used    : 12
% 0.62/0.79  # Proof object initial formulas used   : 6
% 0.62/0.79  # Proof object generating inferences   : 11
% 0.62/0.79  # Proof object simplifying inferences  : 5
% 0.62/0.79  # Training examples: 0 positive, 0 negative
% 0.62/0.79  # Parsed axioms                        : 10
% 0.62/0.79  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.79  # Initial clauses                      : 25
% 0.62/0.79  # Removed in clause preprocessing      : 0
% 0.62/0.79  # Initial clauses in saturation        : 25
% 0.62/0.79  # Processed clauses                    : 4605
% 0.62/0.79  # ...of these trivial                  : 48
% 0.62/0.79  # ...subsumed                          : 3703
% 0.62/0.79  # ...remaining for further processing  : 854
% 0.62/0.79  # Other redundant clauses eliminated   : 20
% 0.62/0.79  # Clauses deleted for lack of memory   : 0
% 0.62/0.79  # Backward-subsumed                    : 58
% 0.62/0.79  # Backward-rewritten                   : 21
% 0.62/0.79  # Generated clauses                    : 20029
% 0.62/0.79  # ...of the previous two non-trivial   : 18650
% 0.62/0.79  # Contextual simplify-reflections      : 38
% 0.62/0.79  # Paramodulations                      : 19699
% 0.62/0.79  # Factorizations                       : 286
% 0.62/0.79  # Equation resolutions                 : 44
% 0.62/0.79  # Propositional unsat checks           : 0
% 0.62/0.79  #    Propositional check models        : 0
% 0.62/0.79  #    Propositional check unsatisfiable : 0
% 0.62/0.79  #    Propositional clauses             : 0
% 0.62/0.79  #    Propositional clauses after purity: 0
% 0.62/0.79  #    Propositional unsat core size     : 0
% 0.62/0.79  #    Propositional preprocessing time  : 0.000
% 0.62/0.79  #    Propositional encoding time       : 0.000
% 0.62/0.79  #    Propositional solver time         : 0.000
% 0.62/0.79  #    Success case prop preproc time    : 0.000
% 0.62/0.79  #    Success case prop encoding time   : 0.000
% 0.62/0.79  #    Success case prop solver time     : 0.000
% 0.62/0.79  # Current number of processed clauses  : 749
% 0.62/0.79  #    Positive orientable unit clauses  : 34
% 0.62/0.79  #    Positive unorientable unit clauses: 0
% 0.62/0.79  #    Negative unit clauses             : 1
% 0.62/0.79  #    Non-unit-clauses                  : 714
% 0.62/0.79  # Current number of unprocessed clauses: 14002
% 0.62/0.79  # ...number of literals in the above   : 60586
% 0.62/0.79  # Current number of archived formulas  : 0
% 0.62/0.79  # Current number of archived clauses   : 103
% 0.62/0.79  # Clause-clause subsumption calls (NU) : 205492
% 0.62/0.79  # Rec. Clause-clause subsumption calls : 104824
% 0.62/0.79  # Non-unit clause-clause subsumptions  : 3798
% 0.62/0.79  # Unit Clause-clause subsumption calls : 711
% 0.62/0.79  # Rewrite failures with RHS unbound    : 0
% 0.62/0.79  # BW rewrite match attempts            : 182
% 0.62/0.79  # BW rewrite match successes           : 17
% 0.62/0.79  # Condensation attempts                : 0
% 0.62/0.79  # Condensation successes               : 0
% 0.62/0.79  # Termbank termtop insertions          : 313706
% 0.62/0.80  
% 0.62/0.80  # -------------------------------------------------
% 0.62/0.80  # User time                : 0.441 s
% 0.62/0.80  # System time              : 0.013 s
% 0.62/0.80  # Total time               : 0.453 s
% 0.62/0.80  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
