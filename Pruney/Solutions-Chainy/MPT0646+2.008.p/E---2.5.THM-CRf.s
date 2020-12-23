%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:43 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 125 expanded)
%              Number of clauses        :   22 (  41 expanded)
%              Number of leaves         :    4 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 953 expanded)
%              Number of equality atoms :   28 ( 155 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   48 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(t49_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
                    & r1_tarski(k2_relat_1(X3),k1_relat_1(X1))
                    & k1_relat_1(X2) = k1_relat_1(X3)
                    & k5_relat_1(X2,X1) = k5_relat_1(X3,X1) )
                 => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).

fof(t53_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(c_0_4,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(k2_relat_1(X8),X7)
      | k5_relat_1(X8,k6_relat_1(X7)) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_5,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ r1_tarski(k2_relat_1(X10),k1_relat_1(X9))
        | ~ r1_tarski(k2_relat_1(X11),k1_relat_1(X9))
        | k1_relat_1(X10) != k1_relat_1(X11)
        | k5_relat_1(X10,X9) != k5_relat_1(X11,X9)
        | X10 = X11
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_relat_1(esk1_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(esk1_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_relat_1(esk2_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(esk2_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r1_tarski(k2_relat_1(esk1_1(X9)),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r1_tarski(k2_relat_1(esk2_1(X9)),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( k1_relat_1(esk1_1(X9)) = k1_relat_1(esk2_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( k5_relat_1(esk1_1(X9),X9) = k5_relat_1(esk2_1(X9),X9)
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk1_1(X9) != esk2_1(X9)
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_funct_1])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ? [X2] :
              ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t53_funct_1])).

cnf(c_0_7,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_relat_1(esk2_1(X1)),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0))
    & ~ v2_funct_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_11,plain,(
    ! [X4,X5,X6] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k5_relat_1(k5_relat_1(X4,X5),X6) = k5_relat_1(X4,k5_relat_1(X5,X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_12,plain,
    ( k5_relat_1(esk2_1(X1),k6_relat_1(k1_relat_1(X1))) = esk2_1(X1)
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k5_relat_1(esk1_1(X1),X1) = k5_relat_1(esk2_1(X1),X1)
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( k5_relat_1(esk2_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk2_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_20,plain,
    ( k5_relat_1(esk2_1(X1),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(esk1_1(X1),X1),X2)
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_relat_1(esk1_1(X1)),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( v1_relat_1(esk1_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( esk2_1(esk3_0) = k5_relat_1(k5_relat_1(esk1_1(esk3_0),esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14]),c_0_21]),c_0_15])]),c_0_16])).

cnf(c_0_26,plain,
    ( k5_relat_1(esk1_1(X1),k6_relat_1(k1_relat_1(X1))) = esk1_1(X1)
    | v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_22]),c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk1_1(esk3_0),esk3_0),esk4_0) != esk1_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(esk1_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk1_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_relat_1(esk1_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_17]),c_0_28]),c_0_21]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_14]),c_0_15])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.14/0.39  # and selection function SelectNewComplexAHP.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.039 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 0.14/0.39  fof(t49_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((((r1_tarski(k2_relat_1(X2),k1_relat_1(X1))&r1_tarski(k2_relat_1(X3),k1_relat_1(X1)))&k1_relat_1(X2)=k1_relat_1(X3))&k5_relat_1(X2,X1)=k5_relat_1(X3,X1))=>X2=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_1)).
% 0.14/0.39  fof(t53_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 0.14/0.39  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.14/0.39  fof(c_0_4, plain, ![X7, X8]:(~v1_relat_1(X8)|(~r1_tarski(k2_relat_1(X8),X7)|k5_relat_1(X8,k6_relat_1(X7))=X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.14/0.39  fof(c_0_5, plain, ![X9, X10, X11]:((~v2_funct_1(X9)|(~v1_relat_1(X10)|~v1_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11)|(~r1_tarski(k2_relat_1(X10),k1_relat_1(X9))|~r1_tarski(k2_relat_1(X11),k1_relat_1(X9))|k1_relat_1(X10)!=k1_relat_1(X11)|k5_relat_1(X10,X9)!=k5_relat_1(X11,X9)|X10=X11)))|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(((v1_relat_1(esk1_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(esk1_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(((v1_relat_1(esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(((((r1_tarski(k2_relat_1(esk1_1(X9)),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(r1_tarski(k2_relat_1(esk2_1(X9)),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(k1_relat_1(esk1_1(X9))=k1_relat_1(esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(k5_relat_1(esk1_1(X9),X9)=k5_relat_1(esk2_1(X9),X9)|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(esk1_1(X9)!=esk2_1(X9)|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_funct_1])])])])])).
% 0.14/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1)))), inference(assume_negation,[status(cth)],[t53_funct_1])).
% 0.14/0.39  cnf(c_0_7, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.39  cnf(c_0_8, plain, (r1_tarski(k2_relat_1(esk2_1(X1)),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_9, plain, (v1_relat_1(esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0)))&~v2_funct_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.14/0.39  fof(c_0_11, plain, ![X4, X5, X6]:(~v1_relat_1(X4)|(~v1_relat_1(X5)|(~v1_relat_1(X6)|k5_relat_1(k5_relat_1(X4,X5),X6)=k5_relat_1(X4,k5_relat_1(X5,X6))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.14/0.39  cnf(c_0_12, plain, (k5_relat_1(esk2_1(X1),k6_relat_1(k1_relat_1(X1)))=esk2_1(X1)|v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_8]), c_0_9])).
% 0.14/0.39  cnf(c_0_13, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_14, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_16, negated_conjecture, (~v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_17, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_18, plain, (k5_relat_1(esk1_1(X1),X1)=k5_relat_1(esk2_1(X1),X1)|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (k5_relat_1(esk2_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk2_1(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.14/0.39  cnf(c_0_20, plain, (k5_relat_1(esk2_1(X1),k5_relat_1(X1,X2))=k5_relat_1(k5_relat_1(esk1_1(X1),X1),X2)|v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_9])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_22, plain, (r1_tarski(k2_relat_1(esk1_1(X1)),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_23, plain, (v1_relat_1(esk1_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_24, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (esk2_1(esk3_0)=k5_relat_1(k5_relat_1(esk1_1(esk3_0),esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_14]), c_0_21]), c_0_15])]), c_0_16])).
% 0.14/0.39  cnf(c_0_26, plain, (k5_relat_1(esk1_1(X1),k6_relat_1(k1_relat_1(X1)))=esk1_1(X1)|v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7, c_0_22]), c_0_23])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (k5_relat_1(k5_relat_1(esk1_1(esk3_0),esk3_0),esk4_0)!=esk1_1(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_14]), c_0_15])]), c_0_16])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (k5_relat_1(esk1_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk1_1(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_13]), c_0_14]), c_0_15])]), c_0_16])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (~v1_relat_1(esk1_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_17]), c_0_28]), c_0_21]), c_0_15])])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_14]), c_0_15])]), c_0_16]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 31
% 0.14/0.39  # Proof object clause steps            : 22
% 0.14/0.39  # Proof object formula steps           : 9
% 0.14/0.39  # Proof object conjectures             : 14
% 0.14/0.39  # Proof object clause conjectures      : 11
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 13
% 0.14/0.39  # Proof object initial formulas used   : 4
% 0.14/0.39  # Proof object generating inferences   : 9
% 0.14/0.39  # Proof object simplifying inferences  : 28
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 4
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 18
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 18
% 0.14/0.39  # Processed clauses                    : 47
% 0.14/0.39  # ...of these trivial                  : 1
% 0.14/0.39  # ...subsumed                          : 0
% 0.14/0.39  # ...remaining for further processing  : 46
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 4
% 0.14/0.39  # Backward-rewritten                   : 4
% 0.14/0.39  # Generated clauses                    : 72
% 0.14/0.39  # ...of the previous two non-trivial   : 68
% 0.14/0.39  # Contextual simplify-reflections      : 5
% 0.14/0.39  # Paramodulations                      : 71
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 1
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 38
% 0.14/0.39  #    Positive orientable unit clauses  : 14
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 3
% 0.14/0.39  #    Non-unit-clauses                  : 21
% 0.14/0.39  # Current number of unprocessed clauses: 39
% 0.14/0.39  # ...number of literals in the above   : 247
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 8
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 145
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 16
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.14/0.39  # Unit Clause-clause subsumption calls : 45
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 2
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 3670
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.007 s
% 0.14/0.39  # Total time               : 0.046 s
% 0.14/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
