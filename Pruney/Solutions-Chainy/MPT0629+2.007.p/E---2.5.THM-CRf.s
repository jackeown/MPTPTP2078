%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:17 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  34 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    5
%              Number of atoms          :  117 ( 186 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t25_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))
           => r2_hidden(X1,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_1)).

fof(c_0_4,plain,(
    ! [X18,X19,X20,X21,X22,X24,X25,X26,X29] :
      ( ( r2_hidden(k4_tarski(X21,esk4_5(X18,X19,X20,X21,X22)),X18)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk4_5(X18,X19,X20,X21,X22),X22),X19)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X24,X26),X18)
        | ~ r2_hidden(k4_tarski(X26,X25),X19)
        | r2_hidden(k4_tarski(X24,X25),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | ~ r2_hidden(k4_tarski(esk5_3(X18,X19,X20),X29),X18)
        | ~ r2_hidden(k4_tarski(X29,esk6_3(X18,X19,X20)),X19)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk7_3(X18,X19,X20)),X18)
        | r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk7_3(X18,X19,X20),esk6_3(X18,X19,X20)),X19)
        | r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | v1_relat_1(k5_relat_1(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X9),X7)
        | X8 != k2_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X12,X11),X7)
        | r2_hidden(X11,X8)
        | X8 != k2_relat_1(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(k4_tarski(X16,esk2_2(X13,X14)),X13)
        | X14 = k2_relat_1(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r2_hidden(k4_tarski(esk3_2(X13,X14),esk2_2(X13,X14)),X13)
        | X14 = k2_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))
             => r2_hidden(X1,k2_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_funct_1])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & r2_hidden(esk8_0,k2_relat_1(k5_relat_1(esk10_0,esk9_0)))
    & ~ r2_hidden(esk8_0,k2_relat_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),esk1_3(k5_relat_1(X1,X2),k2_relat_1(k5_relat_1(X1,X2)),X3),X3),X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k2_relat_1(k5_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(k5_relat_1(esk10_0,esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.20/0.40  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.20/0.40  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.40  fof(t25_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))=>r2_hidden(X1,k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_1)).
% 0.20/0.40  fof(c_0_4, plain, ![X18, X19, X20, X21, X22, X24, X25, X26, X29]:((((r2_hidden(k4_tarski(X21,esk4_5(X18,X19,X20,X21,X22)),X18)|~r2_hidden(k4_tarski(X21,X22),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk4_5(X18,X19,X20,X21,X22),X22),X19)|~r2_hidden(k4_tarski(X21,X22),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18)))&(~r2_hidden(k4_tarski(X24,X26),X18)|~r2_hidden(k4_tarski(X26,X25),X19)|r2_hidden(k4_tarski(X24,X25),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18)))&((~r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)|(~r2_hidden(k4_tarski(esk5_3(X18,X19,X20),X29),X18)|~r2_hidden(k4_tarski(X29,esk6_3(X18,X19,X20)),X19))|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&((r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk7_3(X18,X19,X20)),X18)|r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk7_3(X18,X19,X20),esk6_3(X18,X19,X20)),X19)|r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.20/0.40  fof(c_0_5, plain, ![X31, X32]:(~v1_relat_1(X31)|~v1_relat_1(X32)|v1_relat_1(k5_relat_1(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.40  fof(c_0_6, plain, ![X7, X8, X9, X11, X12, X13, X14, X16]:(((~r2_hidden(X9,X8)|r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X9),X7)|X8!=k2_relat_1(X7))&(~r2_hidden(k4_tarski(X12,X11),X7)|r2_hidden(X11,X8)|X8!=k2_relat_1(X7)))&((~r2_hidden(esk2_2(X13,X14),X14)|~r2_hidden(k4_tarski(X16,esk2_2(X13,X14)),X13)|X14=k2_relat_1(X13))&(r2_hidden(esk2_2(X13,X14),X14)|r2_hidden(k4_tarski(esk3_2(X13,X14),esk2_2(X13,X14)),X13)|X14=k2_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.40  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))=>r2_hidden(X1,k2_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t25_funct_1])).
% 0.20/0.40  cnf(c_0_8, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.20/0.40  cnf(c_0_9, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.40  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.40  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk9_0)&v1_funct_1(esk9_0))&((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&(r2_hidden(esk8_0,k2_relat_1(k5_relat_1(esk10_0,esk9_0)))&~r2_hidden(esk8_0,k2_relat_1(esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.40  cnf(c_0_12, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.40  cnf(c_0_13, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]), c_0_9])).
% 0.20/0.40  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (~r2_hidden(esk8_0,k2_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_16, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.40  cnf(c_0_17, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),esk1_3(k5_relat_1(X1,X2),k2_relat_1(k5_relat_1(X1,X2)),X3),X3),X3),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(X3,k2_relat_1(k5_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (r2_hidden(esk8_0,k2_relat_1(k5_relat_1(esk10_0,esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 23
% 0.20/0.40  # Proof object clause steps            : 14
% 0.20/0.40  # Proof object formula steps           : 9
% 0.20/0.40  # Proof object conjectures             : 9
% 0.20/0.40  # Proof object clause conjectures      : 6
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 8
% 0.20/0.40  # Proof object initial formulas used   : 4
% 0.20/0.40  # Proof object generating inferences   : 3
% 0.20/0.40  # Proof object simplifying inferences  : 8
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 4
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 17
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 17
% 0.20/0.40  # Processed clauses                    : 176
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 52
% 0.20/0.40  # ...remaining for further processing  : 124
% 0.20/0.40  # Other redundant clauses eliminated   : 5
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 612
% 0.20/0.40  # ...of the previous two non-trivial   : 603
% 0.20/0.40  # Contextual simplify-reflections      : 7
% 0.20/0.40  # Paramodulations                      : 605
% 0.20/0.40  # Factorizations                       : 2
% 0.20/0.40  # Equation resolutions                 : 5
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 102
% 0.20/0.40  #    Positive orientable unit clauses  : 5
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 95
% 0.20/0.40  # Current number of unprocessed clauses: 461
% 0.20/0.40  # ...number of literals in the above   : 2144
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 17
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 1712
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 538
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 58
% 0.20/0.40  # Unit Clause-clause subsumption calls : 1
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 0
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 23565
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.049 s
% 0.20/0.40  # System time              : 0.007 s
% 0.20/0.40  # Total time               : 0.057 s
% 0.20/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
