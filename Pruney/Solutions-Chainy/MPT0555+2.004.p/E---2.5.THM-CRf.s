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
% DateTime   : Thu Dec  3 10:51:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   30 (  52 expanded)
%              Number of clauses        :   21 (  22 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :  118 ( 244 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t157_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(c_0_4,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,plain,(
    ! [X11,X12,X13,X15] :
      ( ( r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X13))
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(k4_tarski(esk2_3(X11,X12,X13),X11),X13)
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X12)
        | ~ r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) )
      & ( ~ r2_hidden(X15,k1_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X15,X11),X13)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X11,k9_relat_1(X13,X12))
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(X3,k9_relat_1(X2,X4))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ r1_tarski(X3,X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(k1_relat_1(X16),k1_relat_1(X17))
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r1_tarski(k2_relat_1(X16),k2_relat_1(X17))
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(esk2_3(X1,X5,X4),k1_relat_1(X2))
    | ~ r2_hidden(esk2_3(X1,X5,X4),X3)
    | ~ r2_hidden(X1,k9_relat_1(X4,X5))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ r1_tarski(k1_relat_1(X3),X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(esk2_3(X1,X5,X4),X3)
    | ~ r2_hidden(X1,k9_relat_1(X4,X5))
    | ~ r1_tarski(X4,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( r1_tarski(X2,X3)
             => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t157_relat_1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(X1,k9_relat_1(X4,X3))
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_relat_1(esk5_0)
    & r1_tarski(esk4_0,esk5_0)
    & ~ r1_tarski(k9_relat_1(esk4_0,esk3_0),k9_relat_1(esk5_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X4,X2))
    | r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(k9_relat_1(esk4_0,X1),X2),k9_relat_1(esk5_0,X1))
    | r1_tarski(k9_relat_1(esk4_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk4_0,esk3_0),k9_relat_1(esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk4_0,X1),k9_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.027 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.13/0.39  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.13/0.39  fof(t157_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_relat_1)).
% 0.13/0.39  fof(c_0_4, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_5, plain, ![X11, X12, X13, X15]:((((r2_hidden(esk2_3(X11,X12,X13),k1_relat_1(X13))|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13))&(r2_hidden(k4_tarski(esk2_3(X11,X12,X13),X11),X13)|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13)))&(r2_hidden(esk2_3(X11,X12,X13),X12)|~r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13)))&(~r2_hidden(X15,k1_relat_1(X13))|~r2_hidden(k4_tarski(X15,X11),X13)|~r2_hidden(X15,X12)|r2_hidden(X11,k9_relat_1(X13,X12))|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.13/0.39  cnf(c_0_6, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_7, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_8, plain, (r2_hidden(X3,k9_relat_1(X2,X4))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  cnf(c_0_9, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X4)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~r1_tarski(X3,X4)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.13/0.39  cnf(c_0_10, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  fof(c_0_11, plain, ![X16, X17]:((r1_tarski(k1_relat_1(X16),k1_relat_1(X17))|~r1_tarski(X16,X17)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r1_tarski(k2_relat_1(X16),k2_relat_1(X17))|~r1_tarski(X16,X17)|~v1_relat_1(X17)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.13/0.39  cnf(c_0_12, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~v1_relat_1(X4)|~r2_hidden(esk2_3(X1,X5,X4),k1_relat_1(X2))|~r2_hidden(esk2_3(X1,X5,X4),X3)|~r2_hidden(X1,k9_relat_1(X4,X5))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.13/0.39  cnf(c_0_13, plain, (r2_hidden(esk2_3(X1,X2,X3),X4)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~r1_tarski(k1_relat_1(X3),X4)), inference(spm,[status(thm)],[c_0_6, c_0_10])).
% 0.13/0.39  cnf(c_0_14, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_15, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~v1_relat_1(X4)|~r2_hidden(esk2_3(X1,X5,X4),X3)|~r2_hidden(X1,k9_relat_1(X4,X5))|~r1_tarski(X4,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.13/0.39  cnf(c_0_16, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.39  fof(c_0_17, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X3,X1)))))), inference(assume_negation,[status(cth)],[t157_relat_1])).
% 0.13/0.39  cnf(c_0_18, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~v1_relat_1(X4)|~r2_hidden(X1,k9_relat_1(X4,X3))|~r1_tarski(X4,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.39  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  fof(c_0_20, negated_conjecture, (v1_relat_1(esk4_0)&(v1_relat_1(esk5_0)&(r1_tarski(esk4_0,esk5_0)&~r1_tarski(k9_relat_1(esk4_0,esk3_0),k9_relat_1(esk5_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.39  cnf(c_0_21, plain, (r2_hidden(esk1_2(k9_relat_1(X1,X2),X3),k9_relat_1(X4,X2))|r1_tarski(k9_relat_1(X1,X2),X3)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(k9_relat_1(esk4_0,X1),X2),k9_relat_1(esk5_0,X1))|r1_tarski(k9_relat_1(esk4_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (~r1_tarski(k9_relat_1(esk4_0,esk3_0),k9_relat_1(esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (r1_tarski(k9_relat_1(esk4_0,X1),k9_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 30
% 0.13/0.39  # Proof object clause steps            : 21
% 0.13/0.39  # Proof object formula steps           : 9
% 0.13/0.39  # Proof object conjectures             : 10
% 0.13/0.39  # Proof object clause conjectures      : 7
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 12
% 0.13/0.39  # Proof object initial formulas used   : 4
% 0.13/0.39  # Proof object generating inferences   : 8
% 0.13/0.39  # Proof object simplifying inferences  : 6
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 4
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 13
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 13
% 0.13/0.39  # Processed clauses                    : 195
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 58
% 0.13/0.39  # ...remaining for further processing  : 137
% 0.13/0.39  # Other redundant clauses eliminated   : 0
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 11
% 0.13/0.39  # Backward-rewritten                   : 1
% 0.13/0.39  # Generated clauses                    : 565
% 0.13/0.39  # ...of the previous two non-trivial   : 551
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 565
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 0
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 112
% 0.13/0.39  #    Positive orientable unit clauses  : 14
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 98
% 0.13/0.39  # Current number of unprocessed clauses: 373
% 0.13/0.39  # ...number of literals in the above   : 2033
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 25
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 2544
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 1194
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 71
% 0.13/0.39  # Unit Clause-clause subsumption calls : 42
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 10
% 0.13/0.39  # BW rewrite match successes           : 1
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 15236
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.048 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.052 s
% 0.13/0.39  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
