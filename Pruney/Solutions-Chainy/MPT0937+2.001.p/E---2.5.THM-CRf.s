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
% DateTime   : Thu Dec  3 11:00:40 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   30 (  46 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :  115 ( 181 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

fof(d9_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> r1_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

fof(t2_wellord2,conjecture,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16] :
      ( ( k3_relat_1(X14) = X13
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X14)
        | r1_tarski(X15,X16)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(X15,X16)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | ~ r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_7,plain,(
    ! [X19] : v1_relat_1(k1_wellord2(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r1_relat_2(X7,X8)
        | ~ r2_hidden(X9,X8)
        | r2_hidden(k4_tarski(X9,X9),X7)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk1_2(X7,X10),X10)
        | r1_relat_2(X7,X10)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X10),esk1_2(X7,X10)),X7)
        | r1_relat_2(X7,X10)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X12] :
      ( ( ~ v1_relat_2(X12)
        | r1_relat_2(X12,k3_relat_1(X12))
        | ~ v1_relat_1(X12) )
      & ( ~ r1_relat_2(X12,k3_relat_1(X12))
        | v1_relat_2(X12)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).

cnf(c_0_14,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t2_wellord2])).

cnf(c_0_20,plain,
    ( v1_relat_2(X1)
    | ~ r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_11])])).

cnf(c_0_22,plain,
    ( r1_relat_2(k1_wellord2(X1),X2)
    | ~ r2_hidden(esk1_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_11]),c_0_17])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(k1_wellord2(X1),X2),X2)
    | r1_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

fof(c_0_24,negated_conjecture,(
    ~ v1_relat_2(k1_wellord2(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_25,plain,
    ( v1_relat_2(k1_wellord2(X1))
    | ~ r1_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_11])])).

cnf(c_0_26,plain,
    ( r1_relat_2(k1_wellord2(X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_relat_2(k1_wellord2(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( v1_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.12/0.36  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.36  fof(d1_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_relat_2(X1,X2)<=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(k4_tarski(X3,X3),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 0.12/0.36  fof(d9_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>r1_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_relat_2)).
% 0.12/0.36  fof(t2_wellord2, conjecture, ![X1]:v1_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 0.12/0.36  fof(c_0_6, plain, ![X13, X14, X15, X16]:(((k3_relat_1(X14)=X13|X14!=k1_wellord2(X13)|~v1_relat_1(X14))&((~r2_hidden(k4_tarski(X15,X16),X14)|r1_tarski(X15,X16)|(~r2_hidden(X15,X13)|~r2_hidden(X16,X13))|X14!=k1_wellord2(X13)|~v1_relat_1(X14))&(~r1_tarski(X15,X16)|r2_hidden(k4_tarski(X15,X16),X14)|(~r2_hidden(X15,X13)|~r2_hidden(X16,X13))|X14!=k1_wellord2(X13)|~v1_relat_1(X14))))&(((r2_hidden(esk2_2(X13,X14),X13)|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))&(r2_hidden(esk3_2(X13,X14),X13)|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14)))&((~r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)|~r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)|r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.12/0.36  fof(c_0_7, plain, ![X19]:v1_relat_1(k1_wellord2(X19)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.36  fof(c_0_8, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.36  fof(c_0_9, plain, ![X7, X8, X9, X10]:((~r1_relat_2(X7,X8)|(~r2_hidden(X9,X8)|r2_hidden(k4_tarski(X9,X9),X7))|~v1_relat_1(X7))&((r2_hidden(esk1_2(X7,X10),X10)|r1_relat_2(X7,X10)|~v1_relat_1(X7))&(~r2_hidden(k4_tarski(esk1_2(X7,X10),esk1_2(X7,X10)),X7)|r1_relat_2(X7,X10)|~v1_relat_1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).
% 0.12/0.36  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_12, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  fof(c_0_13, plain, ![X12]:((~v1_relat_2(X12)|r1_relat_2(X12,k3_relat_1(X12))|~v1_relat_1(X12))&(~r1_relat_2(X12,k3_relat_1(X12))|v1_relat_2(X12)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).
% 0.12/0.36  cnf(c_0_14, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_15, plain, (r1_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk1_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])])).
% 0.12/0.36  cnf(c_0_17, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.36  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  fof(c_0_19, negated_conjecture, ~(![X1]:v1_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t2_wellord2])).
% 0.12/0.36  cnf(c_0_20, plain, (v1_relat_2(X1)|~r1_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.36  cnf(c_0_21, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_11])])).
% 0.12/0.36  cnf(c_0_22, plain, (r1_relat_2(k1_wellord2(X1),X2)|~r2_hidden(esk1_2(k1_wellord2(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_11]), c_0_17])])).
% 0.12/0.36  cnf(c_0_23, plain, (r2_hidden(esk1_2(k1_wellord2(X1),X2),X2)|r1_relat_2(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_11])).
% 0.12/0.36  fof(c_0_24, negated_conjecture, ~v1_relat_2(k1_wellord2(esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.12/0.36  cnf(c_0_25, plain, (v1_relat_2(k1_wellord2(X1))|~r1_relat_2(k1_wellord2(X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_11])])).
% 0.12/0.36  cnf(c_0_26, plain, (r1_relat_2(k1_wellord2(X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (~v1_relat_2(k1_wellord2(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.36  cnf(c_0_28, plain, (v1_relat_2(k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 30
% 0.12/0.36  # Proof object clause steps            : 17
% 0.12/0.36  # Proof object formula steps           : 13
% 0.12/0.36  # Proof object conjectures             : 5
% 0.12/0.36  # Proof object clause conjectures      : 2
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 8
% 0.12/0.36  # Proof object initial formulas used   : 6
% 0.12/0.36  # Proof object generating inferences   : 4
% 0.12/0.36  # Proof object simplifying inferences  : 16
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 6
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 17
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 17
% 0.12/0.36  # Processed clauses                    : 47
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 47
% 0.12/0.36  # Other redundant clauses eliminated   : 9
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 1
% 0.12/0.36  # Backward-rewritten                   : 2
% 0.12/0.36  # Generated clauses                    : 23
% 0.12/0.36  # ...of the previous two non-trivial   : 16
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 14
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 9
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 19
% 0.12/0.36  #    Positive orientable unit clauses  : 5
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 14
% 0.12/0.36  # Current number of unprocessed clauses: 2
% 0.12/0.36  # ...number of literals in the above   : 10
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 19
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 55
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 31
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.36  # Unit Clause-clause subsumption calls : 9
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 3
% 0.12/0.36  # BW rewrite match successes           : 2
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1820
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.029 s
% 0.12/0.36  # System time              : 0.004 s
% 0.12/0.36  # Total time               : 0.033 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
