%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:02 EST 2020

% Result     : Theorem 1.15s
% Output     : CNFRefutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   37 (  92 expanded)
%              Number of clauses        :   26 (  41 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 459 expanded)
%              Number of equality atoms :   18 (  78 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t157_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(t158_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(t153_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k9_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k2_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k2_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_relat_1(X34)
      | ~ r1_tarski(X33,X34)
      | r1_tarski(k9_relat_1(X33,X32),k9_relat_1(X34,X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_relat_1])).

cnf(c_0_13,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_relat_1(X31)
      | k9_relat_1(X31,k2_xboole_0(X29,X30)) = k2_xboole_0(k9_relat_1(X31,X29),k9_relat_1(X31,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_19,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_21,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k9_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X4,X2))
    | r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k9_relat_1(X2,k2_xboole_0(X3,X4)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_2(X1,k9_relat_1(X2,k2_xboole_0(X3,X4))),k9_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,X1),X2),k9_relat_1(esk6_0,X1))
    | r1_tarski(k9_relat_1(esk5_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(esk3_0,X1) = X1
    | r2_hidden(esk2_3(esk3_0,X1,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,X1),k9_relat_1(esk6_0,k2_xboole_0(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26])])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_32]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 1.15/1.34  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.15/1.34  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.15/1.34  #
% 1.15/1.34  # Preprocessing time       : 0.027 s
% 1.15/1.34  # Presaturation interreduction done
% 1.15/1.34  
% 1.15/1.34  # Proof found!
% 1.15/1.34  # SZS status Theorem
% 1.15/1.34  # SZS output start CNFRefutation
% 1.15/1.34  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.15/1.34  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.15/1.34  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 1.15/1.34  fof(t158_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 1.15/1.34  fof(t153_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k9_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 1.15/1.34  fof(c_0_5, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 1.15/1.34  fof(c_0_6, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.15/1.34  cnf(c_0_7, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.15/1.34  cnf(c_0_8, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.15/1.34  cnf(c_0_9, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.15/1.34  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.15/1.34  fof(c_0_11, plain, ![X32, X33, X34]:(~v1_relat_1(X33)|(~v1_relat_1(X34)|(~r1_tarski(X33,X34)|r1_tarski(k9_relat_1(X33,X32),k9_relat_1(X34,X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 1.15/1.34  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t158_relat_1])).
% 1.15/1.34  cnf(c_0_13, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 1.15/1.34  cnf(c_0_14, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_7])).
% 1.15/1.34  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 1.15/1.34  cnf(c_0_16, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_8])).
% 1.15/1.34  fof(c_0_17, plain, ![X29, X30, X31]:(~v1_relat_1(X31)|k9_relat_1(X31,k2_xboole_0(X29,X30))=k2_xboole_0(k9_relat_1(X31,X29),k9_relat_1(X31,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).
% 1.15/1.34  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 1.15/1.34  cnf(c_0_19, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.15/1.34  fof(c_0_20, negated_conjecture, (v1_relat_1(esk5_0)&(v1_relat_1(esk6_0)&((r1_tarski(esk5_0,esk6_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 1.15/1.34  cnf(c_0_21, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_14])).
% 1.15/1.34  cnf(c_0_22, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.15/1.34  cnf(c_0_23, plain, (k9_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.15/1.34  cnf(c_0_24, plain, (r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X4,X2))|r1_tarski(k9_relat_1(X1,X2),X3)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 1.15/1.34  cnf(c_0_25, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.15/1.34  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.15/1.34  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.15/1.34  cnf(c_0_28, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_9, c_0_21])).
% 1.15/1.34  cnf(c_0_29, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.15/1.34  cnf(c_0_30, plain, (r1_tarski(X1,k9_relat_1(X2,k2_xboole_0(X3,X4)))|~v1_relat_1(X2)|~r2_hidden(esk1_2(X1,k9_relat_1(X2,k2_xboole_0(X3,X4))),k9_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.15/1.34  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,X1),X2),k9_relat_1(esk6_0,X1))|r1_tarski(k9_relat_1(esk5_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 1.15/1.34  cnf(c_0_32, negated_conjecture, (k2_xboole_0(esk3_0,X1)=X1|r2_hidden(esk2_3(esk3_0,X1,X1),esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.15/1.34  cnf(c_0_33, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,X1),k9_relat_1(esk6_0,k2_xboole_0(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_26])])).
% 1.15/1.34  cnf(c_0_34, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_32]), c_0_32])).
% 1.15/1.34  cnf(c_0_35, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.15/1.34  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 1.15/1.34  # SZS output end CNFRefutation
% 1.15/1.34  # Proof object total steps             : 37
% 1.15/1.34  # Proof object clause steps            : 26
% 1.15/1.34  # Proof object formula steps           : 11
% 1.15/1.34  # Proof object conjectures             : 13
% 1.15/1.34  # Proof object clause conjectures      : 10
% 1.15/1.34  # Proof object formula conjectures     : 3
% 1.15/1.34  # Proof object initial clauses used    : 13
% 1.15/1.34  # Proof object initial formulas used   : 5
% 1.15/1.34  # Proof object generating inferences   : 12
% 1.15/1.34  # Proof object simplifying inferences  : 9
% 1.15/1.34  # Training examples: 0 positive, 0 negative
% 1.15/1.34  # Parsed axioms                        : 9
% 1.15/1.34  # Removed by relevancy pruning/SinE    : 0
% 1.15/1.34  # Initial clauses                      : 22
% 1.15/1.34  # Removed in clause preprocessing      : 0
% 1.15/1.34  # Initial clauses in saturation        : 22
% 1.15/1.34  # Processed clauses                    : 5502
% 1.15/1.34  # ...of these trivial                  : 383
% 1.15/1.34  # ...subsumed                          : 3968
% 1.15/1.34  # ...remaining for further processing  : 1151
% 1.15/1.34  # Other redundant clauses eliminated   : 5
% 1.15/1.34  # Clauses deleted for lack of memory   : 0
% 1.15/1.34  # Backward-subsumed                    : 21
% 1.15/1.34  # Backward-rewritten                   : 3
% 1.15/1.34  # Generated clauses                    : 120170
% 1.15/1.34  # ...of the previous two non-trivial   : 117991
% 1.15/1.34  # Contextual simplify-reflections      : 6
% 1.15/1.34  # Paramodulations                      : 119963
% 1.15/1.34  # Factorizations                       : 202
% 1.15/1.34  # Equation resolutions                 : 5
% 1.15/1.34  # Propositional unsat checks           : 0
% 1.15/1.34  #    Propositional check models        : 0
% 1.15/1.34  #    Propositional check unsatisfiable : 0
% 1.15/1.34  #    Propositional clauses             : 0
% 1.15/1.34  #    Propositional clauses after purity: 0
% 1.15/1.34  #    Propositional unsat core size     : 0
% 1.15/1.34  #    Propositional preprocessing time  : 0.000
% 1.15/1.34  #    Propositional encoding time       : 0.000
% 1.15/1.34  #    Propositional solver time         : 0.000
% 1.15/1.34  #    Success case prop preproc time    : 0.000
% 1.15/1.34  #    Success case prop encoding time   : 0.000
% 1.15/1.34  #    Success case prop solver time     : 0.000
% 1.15/1.34  # Current number of processed clauses  : 1101
% 1.15/1.34  #    Positive orientable unit clauses  : 121
% 1.15/1.34  #    Positive unorientable unit clauses: 1
% 1.15/1.34  #    Negative unit clauses             : 1
% 1.15/1.34  #    Non-unit-clauses                  : 978
% 1.15/1.34  # Current number of unprocessed clauses: 112413
% 1.15/1.34  # ...number of literals in the above   : 324187
% 1.15/1.34  # Current number of archived formulas  : 0
% 1.15/1.34  # Current number of archived clauses   : 45
% 1.15/1.34  # Clause-clause subsumption calls (NU) : 142023
% 1.15/1.34  # Rec. Clause-clause subsumption calls : 107398
% 1.15/1.34  # Non-unit clause-clause subsumptions  : 3991
% 1.15/1.34  # Unit Clause-clause subsumption calls : 1303
% 1.15/1.34  # Rewrite failures with RHS unbound    : 0
% 1.15/1.34  # BW rewrite match attempts            : 705
% 1.15/1.34  # BW rewrite match successes           : 12
% 1.15/1.34  # Condensation attempts                : 0
% 1.15/1.34  # Condensation successes               : 0
% 1.15/1.34  # Termbank termtop insertions          : 3662548
% 1.15/1.34  
% 1.15/1.34  # -------------------------------------------------
% 1.15/1.34  # User time                : 0.931 s
% 1.15/1.34  # System time              : 0.048 s
% 1.15/1.34  # Total time               : 0.979 s
% 1.15/1.34  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
