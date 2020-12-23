%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  74 expanded)
%              Number of clauses        :   22 (  24 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :  160 ( 500 expanded)
%              Number of equality atoms :   46 ( 183 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   48 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t50_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = X1
              & k1_relat_1(X3) = X1
              & r1_tarski(k2_relat_1(X3),X1)
              & v2_funct_1(X2)
              & k5_relat_1(X3,X2) = X2 )
           => X3 = k6_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,plain,(
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

fof(c_0_7,plain,(
    ! [X6] :
      ( k1_relat_1(k6_relat_1(X6)) = X6
      & k2_relat_1(k6_relat_1(X6)) = X6 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_8,plain,(
    ! [X8] :
      ( v1_relat_1(k6_relat_1(X8))
      & v1_funct_1(k6_relat_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = X1
                & k1_relat_1(X3) = X1
                & r1_tarski(k2_relat_1(X3),X1)
                & v2_funct_1(X2)
                & k5_relat_1(X3,X2) = X2 )
             => X3 = k6_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_funct_1])).

cnf(c_0_10,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X3),k1_relat_1(X1))
    | k1_relat_1(X2) != k1_relat_1(X3)
    | k5_relat_1(X2,X1) != k5_relat_1(X3,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & k1_relat_1(esk4_0) = esk3_0
    & k1_relat_1(esk5_0) = esk3_0
    & r1_tarski(k2_relat_1(esk5_0),esk3_0)
    & v2_funct_1(esk4_0)
    & k5_relat_1(esk5_0,esk4_0) = esk4_0
    & esk5_0 != k6_relat_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_16,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k6_relat_1(k1_relat_1(X7)),X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

fof(c_0_17,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k5_relat_1(k6_relat_1(k1_relat_1(X1)),X2) != k5_relat_1(X1,X2)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14])])])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk5_0 != k6_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),X1) != k5_relat_1(esk5_0,X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(esk5_0),k1_relat_1(X1))
    | ~ r1_tarski(esk3_0,k1_relat_1(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk3_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_29,negated_conjecture,
    ( k5_relat_1(esk5_0,esk4_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_25]),c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S0U
% 0.20/0.39  # and selection function SelectComplexExceptRRHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t49_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((((r1_tarski(k2_relat_1(X2),k1_relat_1(X1))&r1_tarski(k2_relat_1(X3),k1_relat_1(X1)))&k1_relat_1(X2)=k1_relat_1(X3))&k5_relat_1(X2,X1)=k5_relat_1(X3,X1))=>X2=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_1)).
% 0.20/0.39  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.39  fof(t50_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 0.20/0.39  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(c_0_6, plain, ![X9, X10, X11]:((~v2_funct_1(X9)|(~v1_relat_1(X10)|~v1_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11)|(~r1_tarski(k2_relat_1(X10),k1_relat_1(X9))|~r1_tarski(k2_relat_1(X11),k1_relat_1(X9))|k1_relat_1(X10)!=k1_relat_1(X11)|k5_relat_1(X10,X9)!=k5_relat_1(X11,X9)|X10=X11)))|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(((v1_relat_1(esk1_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(esk1_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(((v1_relat_1(esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(((((r1_tarski(k2_relat_1(esk1_1(X9)),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(r1_tarski(k2_relat_1(esk2_1(X9)),k1_relat_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(k1_relat_1(esk1_1(X9))=k1_relat_1(esk2_1(X9))|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(k5_relat_1(esk1_1(X9),X9)=k5_relat_1(esk2_1(X9),X9)|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(esk1_1(X9)!=esk2_1(X9)|v2_funct_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_funct_1])])])])])).
% 0.20/0.39  fof(c_0_7, plain, ![X6]:(k1_relat_1(k6_relat_1(X6))=X6&k2_relat_1(k6_relat_1(X6))=X6), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.39  fof(c_0_8, plain, ![X8]:(v1_relat_1(k6_relat_1(X8))&v1_funct_1(k6_relat_1(X8))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1))))), inference(assume_negation,[status(cth)],[t50_funct_1])).
% 0.20/0.39  cnf(c_0_10, plain, (X2=X3|~v2_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~r1_tarski(k2_relat_1(X3),k1_relat_1(X1))|k1_relat_1(X2)!=k1_relat_1(X3)|k5_relat_1(X2,X1)!=k5_relat_1(X3,X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_11, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_12, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_13, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_14, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(((((k1_relat_1(esk4_0)=esk3_0&k1_relat_1(esk5_0)=esk3_0)&r1_tarski(k2_relat_1(esk5_0),esk3_0))&v2_funct_1(esk4_0))&k5_relat_1(esk5_0,esk4_0)=esk4_0)&esk5_0!=k6_relat_1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.39  fof(c_0_16, plain, ![X7]:(~v1_relat_1(X7)|k5_relat_1(k6_relat_1(k1_relat_1(X7)),X7)=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.20/0.39  fof(c_0_17, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_18, plain, (k6_relat_1(k1_relat_1(X1))=X1|k5_relat_1(k6_relat_1(k1_relat_1(X1)),X2)!=k5_relat_1(X1,X2)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14])])])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (esk5_0!=k6_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_23, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k1_relat_1(esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_26, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),X1)!=k5_relat_1(esk5_0,X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(esk5_0),k1_relat_1(X1))|~r1_tarski(esk3_0,k1_relat_1(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.20/0.39  cnf(c_0_28, negated_conjecture, (k5_relat_1(k6_relat_1(esk3_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (k5_relat_1(esk5_0,esk4_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_25]), c_0_32]), c_0_33])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 35
% 0.20/0.39  # Proof object clause steps            : 22
% 0.20/0.39  # Proof object formula steps           : 13
% 0.20/0.39  # Proof object conjectures             : 16
% 0.20/0.39  # Proof object clause conjectures      : 13
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 17
% 0.20/0.39  # Proof object initial formulas used   : 6
% 0.20/0.39  # Proof object generating inferences   : 4
% 0.20/0.39  # Proof object simplifying inferences  : 20
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 6
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 28
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 28
% 0.20/0.39  # Processed clauses                    : 119
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 7
% 0.20/0.39  # ...remaining for further processing  : 112
% 0.20/0.39  # Other redundant clauses eliminated   : 3
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 0
% 0.20/0.39  # Generated clauses                    : 192
% 0.20/0.39  # ...of the previous two non-trivial   : 172
% 0.20/0.39  # Contextual simplify-reflections      : 26
% 0.20/0.39  # Paramodulations                      : 189
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 3
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 83
% 0.20/0.39  #    Positive orientable unit clauses  : 17
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 65
% 0.20/0.39  # Current number of unprocessed clauses: 107
% 0.20/0.39  # ...number of literals in the above   : 646
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 27
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 664
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 312
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 33
% 0.20/0.39  # Unit Clause-clause subsumption calls : 1
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 1
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 6623
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.040 s
% 0.20/0.39  # System time              : 0.005 s
% 0.20/0.39  # Total time               : 0.045 s
% 0.20/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
