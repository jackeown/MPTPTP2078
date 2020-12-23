%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:59 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   40 (  87 expanded)
%              Number of clauses        :   29 (  44 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  110 ( 446 expanded)
%              Number of equality atoms :   24 ( 108 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t153_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k9_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(t156_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

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

fof(c_0_7,plain,(
    ! [X24,X25] : r1_tarski(X24,k2_xboole_0(X24,X25)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_8,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | k9_relat_1(X28,k2_xboole_0(X26,X27)) = k2_xboole_0(k9_relat_1(X28,X26),k9_relat_1(X28,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X2)
    | X3 = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( k9_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r1_tarski(X1,X2)
         => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t156_relat_1])).

cnf(c_0_16,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( X3 = k2_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1)
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_23,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X3,X4)
    | ~ r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X3)
    | ~ r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_19])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X1) = X1
    | r2_hidden(esk2_3(X1,X1,X1),X1) ),
    inference(ef,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X1,k2_xboole_0(X2,X4)))
    | r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(X2,X3)
    | ~ r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_25]),c_0_25])).

cnf(c_0_30,plain,
    ( k2_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,X1),X2),k9_relat_1(esk5_0,k2_xboole_0(X1,X3)))
    | r1_tarski(k9_relat_1(esk5_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k2_xboole_0(esk3_0,X1) = X1
    | r2_hidden(esk2_3(esk3_0,X1,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,X1),k9_relat_1(esk5_0,k2_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.60/0.80  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.60/0.80  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.60/0.80  #
% 0.60/0.80  # Preprocessing time       : 0.027 s
% 0.60/0.80  # Presaturation interreduction done
% 0.60/0.80  
% 0.60/0.80  # Proof found!
% 0.60/0.80  # SZS status Theorem
% 0.60/0.80  # SZS output start CNFRefutation
% 0.60/0.80  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.60/0.80  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.60/0.80  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.60/0.80  fof(t153_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k9_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 0.60/0.80  fof(t156_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.60/0.80  fof(c_0_5, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.60/0.80  fof(c_0_6, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.60/0.80  fof(c_0_7, plain, ![X24, X25]:r1_tarski(X24,k2_xboole_0(X24,X25)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.60/0.80  fof(c_0_8, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|k9_relat_1(X28,k2_xboole_0(X26,X27))=k2_xboole_0(k9_relat_1(X28,X26),k9_relat_1(X28,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).
% 0.60/0.80  cnf(c_0_9, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.60/0.80  cnf(c_0_10, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X2)|X3=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.60/0.80  cnf(c_0_11, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.60/0.80  cnf(c_0_12, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.60/0.80  cnf(c_0_13, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.60/0.80  cnf(c_0_14, plain, (k9_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.80  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t156_relat_1])).
% 0.60/0.80  cnf(c_0_16, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X1)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.60/0.80  cnf(c_0_17, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_9])).
% 0.60/0.80  cnf(c_0_18, plain, (X3=k2_xboole_0(X1,X2)|~r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.60/0.80  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)|r2_hidden(esk2_3(X1,X2,X2),X2)), inference(ef,[status(thm)],[c_0_10])).
% 0.60/0.80  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.60/0.80  cnf(c_0_21, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.60/0.80  fof(c_0_22, negated_conjecture, (v1_relat_1(esk5_0)&(r1_tarski(esk3_0,esk4_0)&~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.60/0.80  cnf(c_0_23, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X3,X4)|~r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X3)|~r2_hidden(esk2_3(X3,X4,k2_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.60/0.80  cnf(c_0_24, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_19])).
% 0.60/0.80  cnf(c_0_25, plain, (k2_xboole_0(X1,X1)=X1|r2_hidden(esk2_3(X1,X1,X1),X1)), inference(ef,[status(thm)],[c_0_19])).
% 0.60/0.80  cnf(c_0_26, plain, (r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X1,k2_xboole_0(X2,X4)))|r1_tarski(k9_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.60/0.80  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.80  cnf(c_0_28, plain, (k2_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(X2,X3)|~r2_hidden(esk2_3(X1,k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.60/0.80  cnf(c_0_29, plain, (k2_xboole_0(X1,X1)=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_25]), c_0_25])).
% 0.60/0.80  cnf(c_0_30, plain, (k2_xboole_0(X1,X2)=X2|r2_hidden(esk2_3(X1,X2,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_11, c_0_24])).
% 0.60/0.80  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.80  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.60/0.80  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,X1),X2),k9_relat_1(esk5_0,k2_xboole_0(X1,X3)))|r1_tarski(k9_relat_1(esk5_0,X1),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.60/0.80  cnf(c_0_34, plain, (k2_xboole_0(X1,X2)=X2|~r2_hidden(esk2_3(X1,X2,X2),X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.60/0.80  cnf(c_0_35, negated_conjecture, (k2_xboole_0(esk3_0,X1)=X1|r2_hidden(esk2_3(esk3_0,X1,X1),esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.60/0.80  cnf(c_0_36, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,X1),k9_relat_1(esk5_0,k2_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.60/0.80  cnf(c_0_37, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.60/0.80  cnf(c_0_38, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.80  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), ['proof']).
% 0.60/0.80  # SZS output end CNFRefutation
% 0.60/0.80  # Proof object total steps             : 40
% 0.60/0.80  # Proof object clause steps            : 29
% 0.60/0.80  # Proof object formula steps           : 11
% 0.60/0.80  # Proof object conjectures             : 11
% 0.60/0.80  # Proof object clause conjectures      : 8
% 0.60/0.80  # Proof object formula conjectures     : 3
% 0.60/0.80  # Proof object initial clauses used    : 12
% 0.60/0.80  # Proof object initial formulas used   : 5
% 0.60/0.80  # Proof object generating inferences   : 16
% 0.60/0.80  # Proof object simplifying inferences  : 4
% 0.60/0.80  # Training examples: 0 positive, 0 negative
% 0.60/0.80  # Parsed axioms                        : 7
% 0.60/0.80  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.80  # Initial clauses                      : 18
% 0.60/0.80  # Removed in clause preprocessing      : 0
% 0.60/0.80  # Initial clauses in saturation        : 18
% 0.60/0.80  # Processed clauses                    : 3742
% 0.60/0.80  # ...of these trivial                  : 601
% 0.60/0.80  # ...subsumed                          : 2539
% 0.60/0.80  # ...remaining for further processing  : 602
% 0.60/0.80  # Other redundant clauses eliminated   : 5
% 0.60/0.80  # Clauses deleted for lack of memory   : 0
% 0.60/0.80  # Backward-subsumed                    : 10
% 0.60/0.80  # Backward-rewritten                   : 5
% 0.60/0.80  # Generated clauses                    : 29333
% 0.60/0.80  # ...of the previous two non-trivial   : 25194
% 0.60/0.80  # Contextual simplify-reflections      : 5
% 0.60/0.80  # Paramodulations                      : 28880
% 0.60/0.80  # Factorizations                       : 448
% 0.60/0.80  # Equation resolutions                 : 5
% 0.60/0.80  # Propositional unsat checks           : 0
% 0.60/0.80  #    Propositional check models        : 0
% 0.60/0.80  #    Propositional check unsatisfiable : 0
% 0.60/0.80  #    Propositional clauses             : 0
% 0.60/0.80  #    Propositional clauses after purity: 0
% 0.60/0.80  #    Propositional unsat core size     : 0
% 0.60/0.80  #    Propositional preprocessing time  : 0.000
% 0.60/0.80  #    Propositional encoding time       : 0.000
% 0.60/0.80  #    Propositional solver time         : 0.000
% 0.60/0.80  #    Success case prop preproc time    : 0.000
% 0.60/0.80  #    Success case prop encoding time   : 0.000
% 0.60/0.80  #    Success case prop solver time     : 0.000
% 0.60/0.80  # Current number of processed clauses  : 565
% 0.60/0.80  #    Positive orientable unit clauses  : 170
% 0.60/0.80  #    Positive unorientable unit clauses: 1
% 0.60/0.80  #    Negative unit clauses             : 1
% 0.60/0.80  #    Non-unit-clauses                  : 393
% 0.60/0.80  # Current number of unprocessed clauses: 21361
% 0.60/0.80  # ...number of literals in the above   : 66161
% 0.60/0.80  # Current number of archived formulas  : 0
% 0.60/0.80  # Current number of archived clauses   : 32
% 0.60/0.80  # Clause-clause subsumption calls (NU) : 45079
% 0.60/0.80  # Rec. Clause-clause subsumption calls : 32760
% 0.60/0.80  # Non-unit clause-clause subsumptions  : 2535
% 0.60/0.80  # Unit Clause-clause subsumption calls : 1087
% 0.60/0.80  # Rewrite failures with RHS unbound    : 0
% 0.60/0.80  # BW rewrite match attempts            : 1608
% 0.60/0.80  # BW rewrite match successes           : 9
% 0.60/0.80  # Condensation attempts                : 0
% 0.60/0.80  # Condensation successes               : 0
% 0.60/0.80  # Termbank termtop insertions          : 479506
% 0.60/0.80  
% 0.60/0.80  # -------------------------------------------------
% 0.60/0.80  # User time                : 0.426 s
% 0.60/0.80  # System time              : 0.026 s
% 0.60/0.80  # Total time               : 0.453 s
% 0.60/0.80  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
