%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:16 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  63 expanded)
%              Number of clauses        :   16 (  23 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  130 ( 284 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d11_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( v1_relat_1(X3)
         => ( X3 = k7_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X4,X2)
                  & r2_hidden(k4_tarski(X4,X5),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(t73_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X1,X2) )
       => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X9,X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(X9,X10),X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X11,X7)
        | ~ r2_hidden(k4_tarski(X11,X12),X6)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk1_3(X6,X7,X8),X7)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_3(X6,X7,X8),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k7_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X1,k1_relat_1(X3))
            & r2_hidden(X1,X2) )
         => r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t73_funct_1])).

fof(c_0_7,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,k1_relat_1(X22))
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X21 = k1_funct_1(X22,X20)
        | ~ r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X20,k1_relat_1(X22))
        | X21 != k1_funct_1(X22,X20)
        | r2_hidden(k4_tarski(X20,X21),X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk3_0,k1_relat_1(esk5_0))
    & r2_hidden(esk3_0,esk4_0)
    & ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),k2_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ( v1_relat_1(k7_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v1_funct_1(k7_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(X15,k1_relat_1(X17))
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(X16,k2_relat_1(X17))
        | ~ r2_hidden(k4_tarski(X15,X16),X17)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,X1),k7_relat_1(X2,esk4_0))
    | ~ r2_hidden(k4_tarski(esk3_0,X1),X2)
    | ~ v1_relat_1(k7_relat_1(X2,esk4_0))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk5_0,esk3_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_17])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk5_0,esk3_0)),k7_relat_1(esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_17])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk5_0,esk3_0),k2_relat_1(k7_relat_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_22])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:51:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.21/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 0.21/0.38  fof(t73_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_1)).
% 0.21/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.21/0.38  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.21/0.38  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.21/0.38  fof(c_0_5, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X9,X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(X9,X10),X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&(~r2_hidden(X11,X7)|~r2_hidden(k4_tarski(X11,X12),X6)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk1_3(X6,X7,X8),X7)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6))|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&((r2_hidden(esk1_3(X6,X7,X8),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k7_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.21/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X1,X2))=>r2_hidden(k1_funct_1(X3,X1),k2_relat_1(k7_relat_1(X3,X2)))))), inference(assume_negation,[status(cth)],[t73_funct_1])).
% 0.21/0.38  fof(c_0_7, plain, ![X20, X21, X22]:(((r2_hidden(X20,k1_relat_1(X22))|~r2_hidden(k4_tarski(X20,X21),X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(X21=k1_funct_1(X22,X20)|~r2_hidden(k4_tarski(X20,X21),X22)|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X20,k1_relat_1(X22))|X21!=k1_funct_1(X22,X20)|r2_hidden(k4_tarski(X20,X21),X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.21/0.38  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X1,X3),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X5!=k7_relat_1(X4,X2)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.38  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((r2_hidden(esk3_0,k1_relat_1(esk5_0))&r2_hidden(esk3_0,esk4_0))&~r2_hidden(k1_funct_1(esk5_0,esk3_0),k2_relat_1(k7_relat_1(esk5_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.21/0.38  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.38  fof(c_0_11, plain, ![X18, X19]:((v1_relat_1(k7_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v1_funct_1(k7_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.21/0.38  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~v1_relat_1(k7_relat_1(X3,X4))|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_13, negated_conjecture, (r2_hidden(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_18, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  fof(c_0_19, plain, ![X15, X16, X17]:((r2_hidden(X15,k1_relat_1(X17))|~r2_hidden(k4_tarski(X15,X16),X17)|~v1_relat_1(X17))&(r2_hidden(X16,k2_relat_1(X17))|~r2_hidden(k4_tarski(X15,X16),X17)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.21/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,X1),k7_relat_1(X2,esk4_0))|~r2_hidden(k4_tarski(esk3_0,X1),X2)|~v1_relat_1(k7_relat_1(X2,esk4_0))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk5_0,esk3_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 0.21/0.38  cnf(c_0_22, negated_conjecture, (v1_relat_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_16]), c_0_17])])).
% 0.21/0.38  cnf(c_0_23, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk5_0,esk3_0)),k7_relat_1(esk5_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_17])])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (~r2_hidden(k1_funct_1(esk5_0,esk3_0),k2_relat_1(k7_relat_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_22])]), c_0_25]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 27
% 0.21/0.38  # Proof object clause steps            : 16
% 0.21/0.38  # Proof object formula steps           : 11
% 0.21/0.38  # Proof object conjectures             : 13
% 0.21/0.38  # Proof object clause conjectures      : 10
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 9
% 0.21/0.38  # Proof object initial formulas used   : 5
% 0.21/0.38  # Proof object generating inferences   : 5
% 0.21/0.38  # Proof object simplifying inferences  : 13
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 5
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 18
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 18
% 0.21/0.38  # Processed clauses                    : 48
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 1
% 0.21/0.38  # ...remaining for further processing  : 47
% 0.21/0.38  # Other redundant clauses eliminated   : 4
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 0
% 0.21/0.38  # Generated clauses                    : 41
% 0.21/0.38  # ...of the previous two non-trivial   : 35
% 0.21/0.38  # Contextual simplify-reflections      : 2
% 0.21/0.38  # Paramodulations                      : 37
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 4
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 26
% 0.21/0.38  #    Positive orientable unit clauses  : 10
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 15
% 0.21/0.38  # Current number of unprocessed clauses: 20
% 0.21/0.38  # ...number of literals in the above   : 80
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 17
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 87
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 35
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 4
% 0.21/0.38  # BW rewrite match successes           : 0
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2606
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.031 s
% 0.21/0.38  # System time              : 0.002 s
% 0.21/0.38  # Total time               : 0.033 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
