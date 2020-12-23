%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:02 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   43 (  66 expanded)
%              Number of clauses        :   26 (  28 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 224 expanded)
%              Number of equality atoms :   18 (  21 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

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

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t153_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k9_relat_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_12,plain,(
    ! [X27,X28] :
      ( ~ r1_tarski(X27,X28)
      | k2_xboole_0(X27,X28) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_13,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X34,X35,X36] :
      ( ~ v1_relat_1(X35)
      | ~ v1_relat_1(X36)
      | ~ r1_tarski(X35,X36)
      | r1_tarski(k9_relat_1(X35,X34),k9_relat_1(X36,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t158_relat_1])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_relat_1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X4,X2))
    | r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X29,X30] : r1_tarski(X29,k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_31,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | k9_relat_1(X33,k2_xboole_0(X31,X32)) = k2_xboole_0(k9_relat_1(X33,X31),k9_relat_1(X33,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk5_0,X1),X2),k9_relat_1(esk6_0,X1))
    | r1_tarski(k9_relat_1(esk5_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k9_relat_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,X1),X2)
    | ~ r1_tarski(k9_relat_1(esk6_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk6_0,esk3_0),k9_relat_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:06:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 2.86/3.09  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.86/3.09  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.86/3.09  #
% 2.86/3.09  # Preprocessing time       : 0.028 s
% 2.86/3.09  # Presaturation interreduction done
% 2.86/3.09  
% 2.86/3.09  # Proof found!
% 2.86/3.09  # SZS status Theorem
% 2.86/3.09  # SZS output start CNFRefutation
% 2.86/3.09  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.86/3.09  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.86/3.09  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.86/3.09  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.86/3.09  fof(t157_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_relat_1)).
% 2.86/3.09  fof(t158_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 2.86/3.09  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.86/3.09  fof(t153_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k9_relat_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 2.86/3.09  fof(c_0_8, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(r2_hidden(X16,X13)|r2_hidden(X16,X14))|X15!=k2_xboole_0(X13,X14))&((~r2_hidden(X17,X13)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))&(~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k2_xboole_0(X13,X14))))&(((~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_xboole_0(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k2_xboole_0(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 2.86/3.09  fof(c_0_9, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 2.86/3.09  cnf(c_0_10, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 2.86/3.09  fof(c_0_11, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 2.86/3.09  fof(c_0_12, plain, ![X27, X28]:(~r1_tarski(X27,X28)|k2_xboole_0(X27,X28)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 2.86/3.09  cnf(c_0_13, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.86/3.09  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.86/3.09  fof(c_0_15, plain, ![X34, X35, X36]:(~v1_relat_1(X35)|(~v1_relat_1(X36)|(~r1_tarski(X35,X36)|r1_tarski(k9_relat_1(X35,X34),k9_relat_1(X36,X34))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t157_relat_1])])])).
% 2.86/3.09  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X4,X2)))))), inference(assume_negation,[status(cth)],[t158_relat_1])).
% 2.86/3.09  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.86/3.09  cnf(c_0_18, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_10])).
% 2.86/3.09  cnf(c_0_19, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.86/3.09  cnf(c_0_20, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.86/3.09  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 2.86/3.09  cnf(c_0_22, plain, (r1_tarski(k9_relat_1(X1,X3),k9_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.86/3.09  fof(c_0_23, negated_conjecture, (v1_relat_1(esk5_0)&(v1_relat_1(esk6_0)&((r1_tarski(esk5_0,esk6_0)&r1_tarski(esk3_0,esk4_0))&~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 2.86/3.09  cnf(c_0_24, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k2_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 2.86/3.09  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 2.86/3.09  cnf(c_0_26, plain, (r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X4,X2))|r1_tarski(k9_relat_1(X1,X2),X3)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.86/3.09  cnf(c_0_27, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.86/3.09  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.86/3.09  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.86/3.09  fof(c_0_30, plain, ![X29, X30]:r1_tarski(X29,k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 2.86/3.09  fof(c_0_31, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|k9_relat_1(X33,k2_xboole_0(X31,X32))=k2_xboole_0(k9_relat_1(X33,X31),k9_relat_1(X33,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t153_relat_1])])).
% 2.86/3.09  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.86/3.09  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk5_0,X1),X2),k9_relat_1(esk6_0,X1))|r1_tarski(k9_relat_1(esk5_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 2.86/3.09  cnf(c_0_34, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.86/3.09  cnf(c_0_35, plain, (k9_relat_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.86/3.09  cnf(c_0_36, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk3_0),k9_relat_1(esk6_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.86/3.09  cnf(c_0_37, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,X1),X2)|~r1_tarski(k9_relat_1(esk6_0,X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 2.86/3.09  cnf(c_0_38, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k2_xboole_0(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 2.86/3.09  cnf(c_0_39, negated_conjecture, (~r1_tarski(k9_relat_1(esk6_0,esk3_0),k9_relat_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 2.86/3.09  cnf(c_0_40, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_20])).
% 2.86/3.09  cnf(c_0_41, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.86/3.09  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_28]), c_0_41])]), ['proof']).
% 2.86/3.09  # SZS output end CNFRefutation
% 2.86/3.09  # Proof object total steps             : 43
% 2.86/3.09  # Proof object clause steps            : 26
% 2.86/3.09  # Proof object formula steps           : 17
% 2.86/3.09  # Proof object conjectures             : 12
% 2.86/3.09  # Proof object clause conjectures      : 9
% 2.86/3.09  # Proof object formula conjectures     : 3
% 2.86/3.09  # Proof object initial clauses used    : 14
% 2.86/3.09  # Proof object initial formulas used   : 8
% 2.86/3.09  # Proof object generating inferences   : 11
% 2.86/3.09  # Proof object simplifying inferences  : 7
% 2.86/3.09  # Training examples: 0 positive, 0 negative
% 2.86/3.09  # Parsed axioms                        : 10
% 2.86/3.09  # Removed by relevancy pruning/SinE    : 0
% 2.86/3.09  # Initial clauses                      : 23
% 2.86/3.09  # Removed in clause preprocessing      : 0
% 2.86/3.09  # Initial clauses in saturation        : 23
% 2.86/3.09  # Processed clauses                    : 38024
% 2.86/3.09  # ...of these trivial                  : 172
% 2.86/3.09  # ...subsumed                          : 34213
% 2.86/3.09  # ...remaining for further processing  : 3639
% 2.86/3.09  # Other redundant clauses eliminated   : 5
% 2.86/3.09  # Clauses deleted for lack of memory   : 0
% 2.86/3.09  # Backward-subsumed                    : 326
% 2.86/3.09  # Backward-rewritten                   : 13
% 2.86/3.09  # Generated clauses                    : 368874
% 2.86/3.09  # ...of the previous two non-trivial   : 349125
% 2.86/3.09  # Contextual simplify-reflections      : 13
% 2.86/3.09  # Paramodulations                      : 368091
% 2.86/3.09  # Factorizations                       : 778
% 2.86/3.09  # Equation resolutions                 : 5
% 2.86/3.09  # Propositional unsat checks           : 0
% 2.86/3.09  #    Propositional check models        : 0
% 2.86/3.09  #    Propositional check unsatisfiable : 0
% 2.86/3.09  #    Propositional clauses             : 0
% 2.86/3.09  #    Propositional clauses after purity: 0
% 2.86/3.09  #    Propositional unsat core size     : 0
% 2.86/3.09  #    Propositional preprocessing time  : 0.000
% 2.86/3.09  #    Propositional encoding time       : 0.000
% 2.86/3.09  #    Propositional solver time         : 0.000
% 2.86/3.09  #    Success case prop preproc time    : 0.000
% 2.86/3.09  #    Success case prop encoding time   : 0.000
% 2.86/3.09  #    Success case prop solver time     : 0.000
% 2.86/3.09  # Current number of processed clauses  : 3273
% 2.86/3.09  #    Positive orientable unit clauses  : 163
% 2.86/3.09  #    Positive unorientable unit clauses: 1
% 2.86/3.09  #    Negative unit clauses             : 48
% 2.86/3.09  #    Non-unit-clauses                  : 3061
% 2.86/3.09  # Current number of unprocessed clauses: 310344
% 2.86/3.09  # ...number of literals in the above   : 1186816
% 2.86/3.09  # Current number of archived formulas  : 0
% 2.86/3.09  # Current number of archived clauses   : 361
% 2.86/3.09  # Clause-clause subsumption calls (NU) : 2027706
% 2.86/3.09  # Rec. Clause-clause subsumption calls : 1008478
% 2.86/3.09  # Non-unit clause-clause subsumptions  : 23897
% 2.86/3.09  # Unit Clause-clause subsumption calls : 25797
% 2.86/3.09  # Rewrite failures with RHS unbound    : 0
% 2.86/3.09  # BW rewrite match attempts            : 4169
% 2.86/3.09  # BW rewrite match successes           : 20
% 2.86/3.09  # Condensation attempts                : 0
% 2.86/3.09  # Condensation successes               : 0
% 2.86/3.09  # Termbank termtop insertions          : 5672834
% 2.93/3.10  
% 2.93/3.10  # -------------------------------------------------
% 2.93/3.10  # User time                : 2.649 s
% 2.93/3.10  # System time              : 0.121 s
% 2.93/3.10  # Total time               : 2.771 s
% 2.93/3.10  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
