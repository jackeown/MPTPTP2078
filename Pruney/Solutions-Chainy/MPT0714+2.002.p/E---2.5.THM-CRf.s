%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:42 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  69 expanded)
%              Number of clauses        :   22 (  29 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 201 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t169_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] : k5_relat_1(k7_relat_1(X1,X3),k7_relat_1(X2,k9_relat_1(X1,X3))) = k7_relat_1(k5_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t112_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k7_relat_1(k5_relat_1(X2,X3),X1) = k5_relat_1(k7_relat_1(X2,X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] : k5_relat_1(k7_relat_1(X1,X3),k7_relat_1(X2,k9_relat_1(X1,X3))) = k7_relat_1(k5_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | k5_relat_1(k5_relat_1(X11,X12),X13) = k5_relat_1(X11,k5_relat_1(X12,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & k5_relat_1(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) != k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,X15) = k5_relat_1(k6_relat_1(X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_12,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | k7_relat_1(k5_relat_1(X7,X8),X6) = k5_relat_1(k7_relat_1(X7,X6),X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).

cnf(c_0_13,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X17] :
      ( v1_relat_1(k6_relat_1(X17))
      & v1_funct_1(k6_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_16,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | v1_relat_1(k7_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_18,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | k2_relat_1(k7_relat_1(X10,X9)) = k9_relat_1(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_19,plain,
    ( k7_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(k7_relat_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,X2),esk2_0) = k5_relat_1(X1,k5_relat_1(X2,esk2_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk2_0) = k7_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_23,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_25,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | k5_relat_1(X14,k6_relat_1(k2_relat_1(X14))) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_26,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( k7_relat_1(k5_relat_1(X1,esk2_0),X2) = k5_relat_1(k7_relat_1(X1,X2),esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,k6_relat_1(X2)),esk2_0) = k5_relat_1(X1,k7_relat_1(esk2_0,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk1_0,X1)) = k9_relat_1(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k5_relat_1(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) != k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k5_relat_1(esk1_0,esk2_0),X1) = k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k5_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),k6_relat_1(X2)),esk2_0) = k5_relat_1(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k5_relat_1(k7_relat_1(esk1_0,X1),k6_relat_1(k9_relat_1(esk1_0,X1))) = k7_relat_1(esk1_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k5_relat_1(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0))) != k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k5_relat_1(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,k9_relat_1(esk1_0,X1))) = k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02AI
% 0.21/0.41  # and selection function SelectNonStrongRROptimalLit.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.026 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t169_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:k5_relat_1(k7_relat_1(X1,X3),k7_relat_1(X2,k9_relat_1(X1,X3)))=k7_relat_1(k5_relat_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_1)).
% 0.21/0.41  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.21/0.41  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.21/0.41  fof(t112_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k7_relat_1(k5_relat_1(X2,X3),X1)=k5_relat_1(k7_relat_1(X2,X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 0.21/0.41  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.21/0.41  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.41  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.21/0.41  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.21/0.41  fof(c_0_8, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:k5_relat_1(k7_relat_1(X1,X3),k7_relat_1(X2,k9_relat_1(X1,X3)))=k7_relat_1(k5_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t169_funct_1])).
% 0.21/0.41  fof(c_0_9, plain, ![X11, X12, X13]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|(~v1_relat_1(X13)|k5_relat_1(k5_relat_1(X11,X12),X13)=k5_relat_1(X11,k5_relat_1(X12,X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.21/0.41  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&k5_relat_1(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))!=k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.41  fof(c_0_11, plain, ![X15, X16]:(~v1_relat_1(X16)|k7_relat_1(X16,X15)=k5_relat_1(k6_relat_1(X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.21/0.41  fof(c_0_12, plain, ![X6, X7, X8]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|k7_relat_1(k5_relat_1(X7,X8),X6)=k5_relat_1(k7_relat_1(X7,X6),X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t112_relat_1])])])).
% 0.21/0.41  cnf(c_0_13, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.41  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  fof(c_0_15, plain, ![X17]:(v1_relat_1(k6_relat_1(X17))&v1_funct_1(k6_relat_1(X17))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.21/0.41  cnf(c_0_16, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  fof(c_0_17, plain, ![X4, X5]:(~v1_relat_1(X4)|v1_relat_1(k7_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.41  fof(c_0_18, plain, ![X9, X10]:(~v1_relat_1(X10)|k2_relat_1(k7_relat_1(X10,X9))=k9_relat_1(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.21/0.41  cnf(c_0_19, plain, (k7_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(k7_relat_1(X1,X3),X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  cnf(c_0_20, negated_conjecture, (k5_relat_1(k5_relat_1(X1,X2),esk2_0)=k5_relat_1(X1,k5_relat_1(X2,esk2_0))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.41  cnf(c_0_21, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_22, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk2_0)=k7_relat_1(esk2_0,X1)), inference(spm,[status(thm)],[c_0_16, c_0_14])).
% 0.21/0.41  cnf(c_0_23, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  fof(c_0_25, plain, ![X14]:(~v1_relat_1(X14)|k5_relat_1(X14,k6_relat_1(k2_relat_1(X14)))=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.21/0.41  cnf(c_0_26, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_27, negated_conjecture, (k7_relat_1(k5_relat_1(X1,esk2_0),X2)=k5_relat_1(k7_relat_1(X1,X2),esk2_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_14])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (k5_relat_1(k5_relat_1(X1,k6_relat_1(X2)),esk2_0)=k5_relat_1(X1,k7_relat_1(esk2_0,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])).
% 0.21/0.41  cnf(c_0_29, negated_conjecture, (v1_relat_1(k7_relat_1(esk1_0,X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.41  cnf(c_0_30, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.41  cnf(c_0_31, negated_conjecture, (k2_relat_1(k7_relat_1(esk1_0,X1))=k9_relat_1(esk1_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.21/0.41  cnf(c_0_32, negated_conjecture, (k5_relat_1(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))!=k7_relat_1(k5_relat_1(esk1_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_33, negated_conjecture, (k7_relat_1(k5_relat_1(esk1_0,esk2_0),X1)=k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.21/0.41  cnf(c_0_34, negated_conjecture, (k5_relat_1(k5_relat_1(k7_relat_1(esk1_0,X1),k6_relat_1(X2)),esk2_0)=k5_relat_1(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.41  cnf(c_0_35, negated_conjecture, (k5_relat_1(k7_relat_1(esk1_0,X1),k6_relat_1(k9_relat_1(esk1_0,X1)))=k7_relat_1(esk1_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_31])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (k5_relat_1(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,k9_relat_1(esk1_0,esk3_0)))!=k5_relat_1(k7_relat_1(esk1_0,esk3_0),esk2_0)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, (k5_relat_1(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,k9_relat_1(esk1_0,X1)))=k5_relat_1(k7_relat_1(esk1_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.41  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 39
% 0.21/0.41  # Proof object clause steps            : 22
% 0.21/0.41  # Proof object formula steps           : 17
% 0.21/0.41  # Proof object conjectures             : 18
% 0.21/0.41  # Proof object clause conjectures      : 15
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 10
% 0.21/0.41  # Proof object initial formulas used   : 8
% 0.21/0.41  # Proof object generating inferences   : 10
% 0.21/0.41  # Proof object simplifying inferences  : 5
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 8
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 13
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 13
% 0.21/0.41  # Processed clauses                    : 408
% 0.21/0.41  # ...of these trivial                  : 35
% 0.21/0.41  # ...subsumed                          : 43
% 0.21/0.41  # ...remaining for further processing  : 330
% 0.21/0.41  # Other redundant clauses eliminated   : 0
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 0
% 0.21/0.41  # Backward-rewritten                   : 4
% 0.21/0.41  # Generated clauses                    : 2159
% 0.21/0.41  # ...of the previous two non-trivial   : 1989
% 0.21/0.41  # Contextual simplify-reflections      : 0
% 0.21/0.41  # Paramodulations                      : 2159
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 0
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 313
% 0.21/0.41  #    Positive orientable unit clauses  : 175
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 0
% 0.21/0.41  #    Non-unit-clauses                  : 138
% 0.21/0.41  # Current number of unprocessed clauses: 1607
% 0.21/0.41  # ...number of literals in the above   : 1900
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 17
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 1878
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1878
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 43
% 0.21/0.41  # Unit Clause-clause subsumption calls : 13
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 162
% 0.21/0.41  # BW rewrite match successes           : 4
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 44115
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.060 s
% 0.21/0.41  # System time              : 0.007 s
% 0.21/0.41  # Total time               : 0.067 s
% 0.21/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
