%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:17 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   29 (  67 expanded)
%              Number of clauses        :   18 (  24 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  124 ( 290 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X1,X2) )
       => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(X1,X2) )
         => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t73_funct_1])).

fof(c_0_6,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ r2_hidden(X20,X21)
      | k1_funct_1(k7_relat_1(X22,X21),X20) = k1_funct_1(X22,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & r2_hidden(esk4_0,k1_relat_1(esk6_0))
    & r2_hidden(esk4_0,esk5_0)
    & ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),k2_relat_1(k7_relat_1(esk6_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X12,X13,X14,X16] :
      ( ( r2_hidden(esk1_3(X8,X9,X10),k1_relat_1(X8))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( X10 = k1_funct_1(X8,esk1_3(X8,X9,X10))
        | ~ r2_hidden(X10,X9)
        | X9 != k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(X13,k1_relat_1(X8))
        | X12 != k1_funct_1(X8,X13)
        | r2_hidden(X12,X9)
        | X9 != k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(esk2_2(X8,X14),X14)
        | ~ r2_hidden(X16,k1_relat_1(X8))
        | esk2_2(X8,X14) != k1_funct_1(X8,X16)
        | X14 = k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk3_2(X8,X14),k1_relat_1(X8))
        | r2_hidden(esk2_2(X8,X14),X14)
        | X14 = k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk2_2(X8,X14) = k1_funct_1(X8,esk3_2(X8,X14))
        | r2_hidden(esk2_2(X8,X14),X14)
        | X14 = k2_relat_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_9,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X18,X19] :
      ( ( v1_relat_1(k7_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(k7_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7] :
      ( ( r2_hidden(X5,X6)
        | ~ r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(X5,k1_relat_1(X7))
        | ~ r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X5,X6)
        | ~ r2_hidden(X5,k1_relat_1(X7))
        | r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk6_0,X1),X2) = k1_funct_1(esk6_0,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk6_0,esk5_0),esk4_0) = k1_funct_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_11])])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk6_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_10]),c_0_11])])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk6_0,esk4_0),k2_relat_1(k7_relat_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k7_relat_1(esk6_0,X2)))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k1_relat_1(k7_relat_1(esk6_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_26])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:48:05 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.12/0.37  # and selection function HSelectMinInfpos.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t73_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 0.12/0.37  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_funct_1)).
% 0.12/0.37  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.12/0.37  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.12/0.37  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2)))))), inference(assume_negation,[status(cth)],[t73_funct_1])).
% 0.12/0.37  fof(c_0_6, plain, ![X20, X21, X22]:(~v1_relat_1(X22)|~v1_funct_1(X22)|(~r2_hidden(X20,X21)|k1_funct_1(k7_relat_1(X22,X21),X20)=k1_funct_1(X22,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 0.12/0.37  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((r2_hidden(esk4_0,k1_relat_1(esk6_0))&r2_hidden(esk4_0,esk5_0))&~r2_hidden(k1_funct_1(esk6_0,esk4_0),k2_relat_1(k7_relat_1(esk6_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X8, X9, X10, X12, X13, X14, X16]:((((r2_hidden(esk1_3(X8,X9,X10),k1_relat_1(X8))|~r2_hidden(X10,X9)|X9!=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(X10=k1_funct_1(X8,esk1_3(X8,X9,X10))|~r2_hidden(X10,X9)|X9!=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(~r2_hidden(X13,k1_relat_1(X8))|X12!=k1_funct_1(X8,X13)|r2_hidden(X12,X9)|X9!=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&((~r2_hidden(esk2_2(X8,X14),X14)|(~r2_hidden(X16,k1_relat_1(X8))|esk2_2(X8,X14)!=k1_funct_1(X8,X16))|X14=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&((r2_hidden(esk3_2(X8,X14),k1_relat_1(X8))|r2_hidden(esk2_2(X8,X14),X14)|X14=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(esk2_2(X8,X14)=k1_funct_1(X8,esk3_2(X8,X14))|r2_hidden(esk2_2(X8,X14),X14)|X14=k2_relat_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.12/0.37  cnf(c_0_9, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  fof(c_0_12, plain, ![X18, X19]:((v1_relat_1(k7_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(k7_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X5, X6, X7]:(((r2_hidden(X5,X6)|~r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))|~v1_relat_1(X7))&(r2_hidden(X5,k1_relat_1(X7))|~r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))|~v1_relat_1(X7)))&(~r2_hidden(X5,X6)|~r2_hidden(X5,k1_relat_1(X7))|r2_hidden(X5,k1_relat_1(k7_relat_1(X7,X6)))|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 0.12/0.37  cnf(c_0_14, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (k1_funct_1(k7_relat_1(esk6_0,X1),X2)=k1_funct_1(esk6_0,X2)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_17, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_18, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, plain, (r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_20, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (k1_funct_1(k7_relat_1(esk6_0,esk5_0),esk4_0)=k1_funct_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_1(k7_relat_1(esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_10]), c_0_11])])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (v1_relat_1(k7_relat_1(esk6_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_10]), c_0_11])])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (~r2_hidden(k1_funct_1(esk6_0,esk4_0),k2_relat_1(k7_relat_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,k1_relat_1(k7_relat_1(esk6_0,X2)))|~r2_hidden(X1,k1_relat_1(esk6_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_19, c_0_11])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk4_0,k1_relat_1(k7_relat_1(esk6_0,esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_16]), c_0_26])]), c_0_27]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 29
% 0.12/0.37  # Proof object clause steps            : 18
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 15
% 0.12/0.37  # Proof object clause conjectures      : 12
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 10
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 7
% 0.12/0.37  # Proof object simplifying inferences  : 15
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 17
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 17
% 0.12/0.37  # Processed clauses                    : 55
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 55
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 57
% 0.12/0.37  # ...of the previous two non-trivial   : 51
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 54
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 4
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
% 0.12/0.37  # Current number of processed clauses  : 35
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 2
% 0.12/0.37  #    Non-unit-clauses                  : 20
% 0.12/0.37  # Current number of unprocessed clauses: 30
% 0.12/0.37  # ...number of literals in the above   : 70
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 17
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 49
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 24
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 6
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2751
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
