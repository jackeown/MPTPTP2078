%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:39 EST 2020

% Result     : Theorem 0.06s
% Output     : CNFRefutation 0.06s
% Verified   : 
% Statistics : Number of formulae       :   32 (  79 expanded)
%              Number of clauses        :   19 (  27 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 452 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_ordinal1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v5_ordinal1(X2) )
     => ! [X3] :
          ( v3_ordinal1(X3)
         => ( v1_relat_1(k7_relat_1(X2,X3))
            & v5_relat_1(k7_relat_1(X2,X3),X1)
            & v1_funct_1(k7_relat_1(X2,X3))
            & v5_ordinal1(k7_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_ordinal1)).

fof(fc25_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_relat_1(X3) )
     => ( v1_relat_1(k5_relat_1(X3,X2))
        & v5_relat_1(k5_relat_1(X3,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc25_relat_1)).

fof(fc5_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v5_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v5_relat_1(k7_relat_1(X1,X2),k2_relat_1(X1))
        & v5_ordinal1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_ordinal1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(fc24_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v4_relat_1(k6_relat_1(X1),X1)
      & v5_relat_1(k6_relat_1(X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v5_relat_1(X2,X1)
          & v1_funct_1(X2)
          & v5_ordinal1(X2) )
       => ! [X3] :
            ( v3_ordinal1(X3)
           => ( v1_relat_1(k7_relat_1(X2,X3))
              & v5_relat_1(k7_relat_1(X2,X3),X1)
              & v1_funct_1(k7_relat_1(X2,X3))
              & v5_ordinal1(k7_relat_1(X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_ordinal1])).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( ( v1_relat_1(k5_relat_1(X9,X8))
        | ~ v1_relat_1(X8)
        | ~ v5_relat_1(X8,X7)
        | ~ v1_relat_1(X9) )
      & ( v5_relat_1(k5_relat_1(X9,X8),X7)
        | ~ v1_relat_1(X8)
        | ~ v5_relat_1(X8,X7)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc25_relat_1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v5_relat_1(esk2_0,esk1_0)
    & v1_funct_1(esk2_0)
    & v5_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0))
      | ~ v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)
      | ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
      | ~ v5_ordinal1(k7_relat_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X15,X16] :
      ( ( v1_relat_1(k7_relat_1(X15,X16))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v5_ordinal1(X15)
        | ~ v3_ordinal1(X16) )
      & ( v5_relat_1(k7_relat_1(X15,X16),k2_relat_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v5_ordinal1(X15)
        | ~ v3_ordinal1(X16) )
      & ( v5_ordinal1(k7_relat_1(X15,X16))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v5_ordinal1(X15)
        | ~ v3_ordinal1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_ordinal1])])])).

cnf(c_0_10,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v5_relat_1(X2,X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | k7_relat_1(X5,X4) = k5_relat_1(k6_relat_1(X4),X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_14,plain,(
    ! [X6] :
      ( v1_relat_1(k6_relat_1(X6))
      & v4_relat_1(k6_relat_1(X6),X6)
      & v5_relat_1(k6_relat_1(X6),X6) ) ),
    inference(variable_rename,[status(thm)],[fc24_relat_1])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v5_ordinal1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v5_ordinal1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v5_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v5_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_21,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_12])])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_12])])).

cnf(c_0_25,plain,
    ( v5_relat_1(k5_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X2)
    | ~ v5_relat_1(X2,X3)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0))
    | ~ v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24])])).

cnf(c_0_27,plain,
    ( v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_22])])).

fof(c_0_28,plain,(
    ! [X13,X14] :
      ( ( v1_relat_1(k7_relat_1(X13,X14))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( v1_funct_1(k7_relat_1(X13,X14))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_1(k7_relat_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_11]),c_0_12])])).

cnf(c_0_30,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19]),c_0_12])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.25  % Computer   : n006.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 16:49:07 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  # Version: 2.5pre002
% 0.06/0.25  # No SInE strategy applied
% 0.06/0.25  # Trying AutoSched0 for 299 seconds
% 0.06/0.27  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.06/0.27  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.06/0.27  #
% 0.06/0.27  # Preprocessing time       : 0.013 s
% 0.06/0.27  # Presaturation interreduction done
% 0.06/0.27  
% 0.06/0.27  # Proof found!
% 0.06/0.27  # SZS status Theorem
% 0.06/0.27  # SZS output start CNFRefutation
% 0.06/0.27  fof(t48_ordinal1, conjecture, ![X1, X2]:((((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))&v5_ordinal1(X2))=>![X3]:(v3_ordinal1(X3)=>(((v1_relat_1(k7_relat_1(X2,X3))&v5_relat_1(k7_relat_1(X2,X3),X1))&v1_funct_1(k7_relat_1(X2,X3)))&v5_ordinal1(k7_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_ordinal1)).
% 0.06/0.27  fof(fc25_relat_1, axiom, ![X1, X2, X3]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_relat_1(X3))=>(v1_relat_1(k5_relat_1(X3,X2))&v5_relat_1(k5_relat_1(X3,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc25_relat_1)).
% 0.06/0.27  fof(fc5_ordinal1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v5_ordinal1(X1))&v3_ordinal1(X2))=>((v1_relat_1(k7_relat_1(X1,X2))&v5_relat_1(k7_relat_1(X1,X2),k2_relat_1(X1)))&v5_ordinal1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_ordinal1)).
% 0.06/0.27  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 0.06/0.27  fof(fc24_relat_1, axiom, ![X1]:((v1_relat_1(k6_relat_1(X1))&v4_relat_1(k6_relat_1(X1),X1))&v5_relat_1(k6_relat_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc24_relat_1)).
% 0.06/0.27  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.06/0.27  fof(c_0_6, negated_conjecture, ~(![X1, X2]:((((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))&v5_ordinal1(X2))=>![X3]:(v3_ordinal1(X3)=>(((v1_relat_1(k7_relat_1(X2,X3))&v5_relat_1(k7_relat_1(X2,X3),X1))&v1_funct_1(k7_relat_1(X2,X3)))&v5_ordinal1(k7_relat_1(X2,X3)))))), inference(assume_negation,[status(cth)],[t48_ordinal1])).
% 0.06/0.27  fof(c_0_7, plain, ![X7, X8, X9]:((v1_relat_1(k5_relat_1(X9,X8))|(~v1_relat_1(X8)|~v5_relat_1(X8,X7)|~v1_relat_1(X9)))&(v5_relat_1(k5_relat_1(X9,X8),X7)|(~v1_relat_1(X8)|~v5_relat_1(X8,X7)|~v1_relat_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc25_relat_1])])])).
% 0.06/0.27  fof(c_0_8, negated_conjecture, ((((v1_relat_1(esk2_0)&v5_relat_1(esk2_0,esk1_0))&v1_funct_1(esk2_0))&v5_ordinal1(esk2_0))&(v3_ordinal1(esk3_0)&(~v1_relat_1(k7_relat_1(esk2_0,esk3_0))|~v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)|~v1_funct_1(k7_relat_1(esk2_0,esk3_0))|~v5_ordinal1(k7_relat_1(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.06/0.27  fof(c_0_9, plain, ![X15, X16]:(((v1_relat_1(k7_relat_1(X15,X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v5_ordinal1(X15)|~v3_ordinal1(X16)))&(v5_relat_1(k7_relat_1(X15,X16),k2_relat_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v5_ordinal1(X15)|~v3_ordinal1(X16))))&(v5_ordinal1(k7_relat_1(X15,X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v5_ordinal1(X15)|~v3_ordinal1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc5_ordinal1])])])).
% 0.06/0.27  cnf(c_0_10, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v5_relat_1(X2,X3)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.06/0.27  cnf(c_0_11, negated_conjecture, (v5_relat_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.06/0.27  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.06/0.27  fof(c_0_13, plain, ![X4, X5]:(~v1_relat_1(X5)|k7_relat_1(X5,X4)=k5_relat_1(k6_relat_1(X4),X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.06/0.27  fof(c_0_14, plain, ![X6]:((v1_relat_1(k6_relat_1(X6))&v4_relat_1(k6_relat_1(X6),X6))&v5_relat_1(k6_relat_1(X6),X6)), inference(variable_rename,[status(thm)],[fc24_relat_1])).
% 0.06/0.27  cnf(c_0_15, negated_conjecture, (~v1_relat_1(k7_relat_1(esk2_0,esk3_0))|~v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)|~v1_funct_1(k7_relat_1(esk2_0,esk3_0))|~v5_ordinal1(k7_relat_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.06/0.27  cnf(c_0_16, plain, (v5_ordinal1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v5_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.06/0.27  cnf(c_0_17, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.06/0.27  cnf(c_0_18, negated_conjecture, (v5_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.06/0.27  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.06/0.27  cnf(c_0_20, negated_conjecture, (v1_relat_1(k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.06/0.27  cnf(c_0_21, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.06/0.27  cnf(c_0_22, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.06/0.27  cnf(c_0_23, negated_conjecture, (~v1_funct_1(k7_relat_1(esk2_0,esk3_0))|~v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)|~v1_relat_1(k7_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_12])])).
% 0.06/0.27  cnf(c_0_24, negated_conjecture, (v1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_12])])).
% 0.06/0.27  cnf(c_0_25, plain, (v5_relat_1(k5_relat_1(X1,X2),X3)|~v1_relat_1(X2)|~v5_relat_1(X2,X3)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.06/0.27  cnf(c_0_26, negated_conjecture, (~v1_funct_1(k7_relat_1(esk2_0,esk3_0))|~v5_relat_1(k7_relat_1(esk2_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24])])).
% 0.06/0.27  cnf(c_0_27, plain, (v5_relat_1(k7_relat_1(X1,X2),X3)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_22])])).
% 0.06/0.27  fof(c_0_28, plain, ![X13, X14]:((v1_relat_1(k7_relat_1(X13,X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(v1_funct_1(k7_relat_1(X13,X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.06/0.27  cnf(c_0_29, negated_conjecture, (~v1_funct_1(k7_relat_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_11]), c_0_12])])).
% 0.06/0.27  cnf(c_0_30, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.06/0.27  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19]), c_0_12])]), ['proof']).
% 0.06/0.27  # SZS output end CNFRefutation
% 0.06/0.27  # Proof object total steps             : 32
% 0.06/0.27  # Proof object clause steps            : 19
% 0.06/0.27  # Proof object formula steps           : 13
% 0.06/0.27  # Proof object conjectures             : 15
% 0.06/0.27  # Proof object clause conjectures      : 12
% 0.06/0.27  # Proof object formula conjectures     : 3
% 0.06/0.27  # Proof object initial clauses used    : 12
% 0.06/0.27  # Proof object initial formulas used   : 6
% 0.06/0.27  # Proof object generating inferences   : 6
% 0.06/0.27  # Proof object simplifying inferences  : 20
% 0.06/0.27  # Training examples: 0 positive, 0 negative
% 0.06/0.27  # Parsed axioms                        : 8
% 0.06/0.27  # Removed by relevancy pruning/SinE    : 0
% 0.06/0.27  # Initial clauses                      : 21
% 0.06/0.27  # Removed in clause preprocessing      : 0
% 0.06/0.27  # Initial clauses in saturation        : 21
% 0.06/0.27  # Processed clauses                    : 52
% 0.06/0.27  # ...of these trivial                  : 1
% 0.06/0.27  # ...subsumed                          : 3
% 0.06/0.27  # ...remaining for further processing  : 48
% 0.06/0.27  # Other redundant clauses eliminated   : 0
% 0.06/0.27  # Clauses deleted for lack of memory   : 0
% 0.06/0.27  # Backward-subsumed                    : 1
% 0.06/0.27  # Backward-rewritten                   : 1
% 0.06/0.27  # Generated clauses                    : 20
% 0.06/0.27  # ...of the previous two non-trivial   : 20
% 0.06/0.27  # Contextual simplify-reflections      : 1
% 0.06/0.27  # Paramodulations                      : 20
% 0.06/0.27  # Factorizations                       : 0
% 0.06/0.27  # Equation resolutions                 : 0
% 0.06/0.27  # Propositional unsat checks           : 0
% 0.06/0.27  #    Propositional check models        : 0
% 0.06/0.27  #    Propositional check unsatisfiable : 0
% 0.06/0.27  #    Propositional clauses             : 0
% 0.06/0.27  #    Propositional clauses after purity: 0
% 0.06/0.27  #    Propositional unsat core size     : 0
% 0.06/0.27  #    Propositional preprocessing time  : 0.000
% 0.06/0.27  #    Propositional encoding time       : 0.000
% 0.06/0.27  #    Propositional solver time         : 0.000
% 0.06/0.27  #    Success case prop preproc time    : 0.000
% 0.06/0.27  #    Success case prop encoding time   : 0.000
% 0.06/0.27  #    Success case prop solver time     : 0.000
% 0.06/0.27  # Current number of processed clauses  : 27
% 0.06/0.27  #    Positive orientable unit clauses  : 11
% 0.06/0.27  #    Positive unorientable unit clauses: 0
% 0.06/0.27  #    Negative unit clauses             : 1
% 0.06/0.27  #    Non-unit-clauses                  : 15
% 0.06/0.27  # Current number of unprocessed clauses: 8
% 0.06/0.27  # ...number of literals in the above   : 41
% 0.06/0.27  # Current number of archived formulas  : 0
% 0.06/0.27  # Current number of archived clauses   : 21
% 0.06/0.27  # Clause-clause subsumption calls (NU) : 39
% 0.06/0.27  # Rec. Clause-clause subsumption calls : 13
% 0.06/0.27  # Non-unit clause-clause subsumptions  : 5
% 0.06/0.27  # Unit Clause-clause subsumption calls : 1
% 0.06/0.27  # Rewrite failures with RHS unbound    : 0
% 0.06/0.27  # BW rewrite match attempts            : 1
% 0.06/0.27  # BW rewrite match successes           : 1
% 0.06/0.27  # Condensation attempts                : 0
% 0.06/0.27  # Condensation successes               : 0
% 0.06/0.27  # Termbank termtop insertions          : 1841
% 0.06/0.27  
% 0.06/0.27  # -------------------------------------------------
% 0.06/0.27  # User time                : 0.014 s
% 0.06/0.27  # System time              : 0.002 s
% 0.06/0.27  # Total time               : 0.016 s
% 0.06/0.27  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
