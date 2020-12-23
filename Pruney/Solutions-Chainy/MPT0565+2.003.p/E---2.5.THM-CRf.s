%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  86 expanded)
%              Number of clauses        :   16 (  40 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 370 expanded)
%              Number of equality atoms :   22 (  99 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t169_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(c_0_4,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X18),X16)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(esk5_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) )
      & ( r2_hidden(esk5_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)
        | X12 = k1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)
        | X12 = k1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X27,X28,X29,X31] :
      ( ( r2_hidden(esk7_3(X27,X28,X29),k2_relat_1(X29))
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(X27,esk7_3(X27,X28,X29)),X29)
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk7_3(X27,X28,X29),X28)
        | ~ r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(X31,k2_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X31),X29)
        | ~ r2_hidden(X31,X28)
        | r2_hidden(X27,k10_relat_1(X29,X28))
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),k2_relat_1(X2))
    | r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk2_2(X2,X1),X1)
    | r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,esk3_2(X2,X1)),X2)
    | ~ r2_hidden(esk3_2(X2,X1),X4) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t169_relat_1])).

cnf(c_0_14,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(X3,k10_relat_1(X2,k2_relat_1(X2)))
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,esk3_2(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & k10_relat_1(esk8_0,k2_relat_1(esk8_0)) != k1_relat_1(esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_16,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk2_2(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( X1 = k1_relat_1(esk8_0)
    | r2_hidden(esk2_2(esk8_0,X1),k10_relat_1(esk8_0,k2_relat_1(esk8_0)))
    | r2_hidden(esk2_2(esk8_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( k10_relat_1(esk8_0,k2_relat_1(esk8_0)) != k1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_2(esk8_0,k10_relat_1(esk8_0,k2_relat_1(esk8_0))),k10_relat_1(esk8_0,k2_relat_1(esk8_0))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_18]),c_0_19])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_2(esk8_0,k10_relat_1(esk8_0,k2_relat_1(esk8_0))),X1),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_17])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S070I
% 0.19/0.38  # and selection function SelectVGNonCR.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.38  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.19/0.38  fof(t169_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.19/0.38  fof(c_0_4, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X18),X16)|X17!=k2_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)))&((~r2_hidden(esk5_2(X22,X23),X23)|~r2_hidden(k4_tarski(X25,esk5_2(X22,X23)),X22)|X23=k2_relat_1(X22))&(r2_hidden(esk5_2(X22,X23),X23)|r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)|X23=k2_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.38  cnf(c_0_5, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.38  fof(c_0_6, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)|X6!=k1_relat_1(X5))&(~r2_hidden(k4_tarski(X9,X10),X5)|r2_hidden(X9,X6)|X6!=k1_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)|X12=k1_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)|X12=k1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.38  fof(c_0_7, plain, ![X27, X28, X29, X31]:((((r2_hidden(esk7_3(X27,X28,X29),k2_relat_1(X29))|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29))&(r2_hidden(k4_tarski(X27,esk7_3(X27,X28,X29)),X29)|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29)))&(r2_hidden(esk7_3(X27,X28,X29),X28)|~r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29)))&(~r2_hidden(X31,k2_relat_1(X29))|~r2_hidden(k4_tarski(X27,X31),X29)|~r2_hidden(X31,X28)|r2_hidden(X27,k10_relat_1(X29,X28))|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.19/0.38  cnf(c_0_8, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_9, plain, (r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_10, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_11, plain, (X1=k1_relat_1(X2)|r2_hidden(esk3_2(X2,X1),k2_relat_1(X2))|r2_hidden(esk2_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.19/0.38  cnf(c_0_12, plain, (X1=k1_relat_1(X2)|r2_hidden(esk2_2(X2,X1),X1)|r2_hidden(X3,k10_relat_1(X2,X4))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,esk3_2(X2,X1)),X2)|~r2_hidden(esk3_2(X2,X1),X4)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1))), inference(assume_negation,[status(cth)],[t169_relat_1])).
% 0.19/0.38  cnf(c_0_14, plain, (X1=k1_relat_1(X2)|r2_hidden(X3,k10_relat_1(X2,k2_relat_1(X2)))|r2_hidden(esk2_2(X2,X1),X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,esk3_2(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_12, c_0_11])).
% 0.19/0.38  fof(c_0_15, negated_conjecture, (v1_relat_1(esk8_0)&k10_relat_1(esk8_0,k2_relat_1(esk8_0))!=k1_relat_1(esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.38  cnf(c_0_16, plain, (X1=k1_relat_1(X2)|r2_hidden(esk2_2(X2,X1),k10_relat_1(X2,k2_relat_1(X2)))|r2_hidden(esk2_2(X2,X1),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_14, c_0_9])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (X1=k1_relat_1(esk8_0)|r2_hidden(esk2_2(esk8_0,X1),k10_relat_1(esk8_0,k2_relat_1(esk8_0)))|r2_hidden(esk2_2(esk8_0,X1),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (k10_relat_1(esk8_0,k2_relat_1(esk8_0))!=k1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_20, plain, (X2=k1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(esk2_2(esk8_0,k10_relat_1(esk8_0,k2_relat_1(esk8_0))),k10_relat_1(esk8_0,k2_relat_1(esk8_0)))), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_18]), c_0_19])).
% 0.19/0.38  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (~r2_hidden(k4_tarski(esk2_2(esk8_0,k10_relat_1(esk8_0,k2_relat_1(esk8_0))),X1),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_19])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_21]), c_0_17])]), c_0_23]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 25
% 0.19/0.38  # Proof object clause steps            : 16
% 0.19/0.38  # Proof object formula steps           : 9
% 0.19/0.38  # Proof object conjectures             : 9
% 0.19/0.38  # Proof object clause conjectures      : 6
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 7
% 0.19/0.38  # Proof object initial formulas used   : 4
% 0.19/0.38  # Proof object generating inferences   : 9
% 0.19/0.38  # Proof object simplifying inferences  : 5
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 4
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 14
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 14
% 0.19/0.38  # Processed clauses                    : 93
% 0.19/0.38  # ...of these trivial                  : 4
% 0.19/0.38  # ...subsumed                          : 7
% 0.19/0.38  # ...remaining for further processing  : 81
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 169
% 0.19/0.38  # ...of the previous two non-trivial   : 164
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 150
% 0.19/0.38  # Factorizations                       : 6
% 0.19/0.38  # Equation resolutions                 : 13
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 67
% 0.19/0.38  #    Positive orientable unit clauses  : 3
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 61
% 0.19/0.38  # Current number of unprocessed clauses: 99
% 0.19/0.38  # ...number of literals in the above   : 431
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 14
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 392
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 99
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 9
% 0.19/0.38  # Unit Clause-clause subsumption calls : 1
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5982
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.040 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
