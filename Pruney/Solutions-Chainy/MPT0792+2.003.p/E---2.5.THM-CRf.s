%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:57 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  76 expanded)
%              Number of clauses        :   20 (  27 expanded)
%              Number of leaves         :    5 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 513 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t42_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3))
          & ! [X4] :
              ( r2_hidden(X4,k1_wellord1(X3,X1))
             => ( r2_hidden(k4_tarski(X4,X2),X3)
                & X4 != X2 ) ) )
       => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_wellord1)).

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3))
            & ! [X4] :
                ( r2_hidden(X4,k1_wellord1(X3,X1))
               => ( r2_hidden(k4_tarski(X4,X2),X3)
                  & X4 != X2 ) ) )
         => r2_hidden(k4_tarski(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t42_wellord1])).

fof(c_0_6,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v6_relat_2(X17)
        | ~ r2_hidden(X18,k3_relat_1(X17))
        | ~ r2_hidden(X19,k3_relat_1(X17))
        | X18 = X19
        | r2_hidden(k4_tarski(X18,X19),X17)
        | r2_hidden(k4_tarski(X19,X18),X17)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk3_1(X17),k3_relat_1(X17))
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk4_1(X17),k3_relat_1(X17))
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( esk3_1(X17) != esk4_1(X17)
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X17),esk4_1(X17)),X17)
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk4_1(X17),esk3_1(X17)),X17)
        | v6_relat_2(X17)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X25] :
      ( v1_relat_1(esk7_0)
      & v2_wellord1(esk7_0)
      & r2_hidden(esk5_0,k3_relat_1(esk7_0))
      & r2_hidden(esk6_0,k3_relat_1(esk7_0))
      & ( r2_hidden(k4_tarski(X25,esk6_0),esk7_0)
        | ~ r2_hidden(X25,k1_wellord1(esk7_0,esk5_0)) )
      & ( X25 != esk6_0
        | ~ r2_hidden(X25,k1_wellord1(esk7_0,esk5_0)) )
      & ~ r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

cnf(c_0_8,plain,
    ( X2 = X3
    | r2_hidden(k4_tarski(X2,X3),X1)
    | r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk6_0,k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X13] :
      ( ( v1_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v8_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v4_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v6_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v1_wellord1(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( ~ v1_relat_2(X13)
        | ~ v8_relat_2(X13)
        | ~ v4_relat_2(X13)
        | ~ v6_relat_2(X13)
        | ~ v1_wellord1(X13)
        | v2_wellord1(X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11] :
      ( ( X8 != X6
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(X8,X6),X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( X9 = X6
        | ~ r2_hidden(k4_tarski(X9,X6),X5)
        | r2_hidden(X9,X7)
        | X7 != k1_wellord1(X5,X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(esk1_3(X5,X10,X11),X11)
        | esk1_3(X5,X10,X11) = X10
        | ~ r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( esk1_3(X5,X10,X11) != X10
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)
        | r2_hidden(esk1_3(X5,X10,X11),X11)
        | X11 = k1_wellord1(X5,X10)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_13,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(k4_tarski(esk6_0,X1),esk7_0)
    | r2_hidden(k4_tarski(X1,esk6_0),esk7_0)
    | ~ v6_relat_2(esk7_0)
    | ~ r2_hidden(X1,k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_wellord1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk6_0
    | r2_hidden(k4_tarski(X1,esk6_0),esk7_0)
    | r2_hidden(k4_tarski(esk6_0,X1),esk7_0)
    | ~ r2_hidden(X1,k3_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_10])])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk5_0,k3_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( X1 != esk6_0
    | ~ r2_hidden(X1,k1_wellord1(esk7_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( esk6_0 = esk5_0
    | r2_hidden(k4_tarski(esk6_0,esk5_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_10])]),c_0_23])).

fof(c_0_25,plain,(
    ! [X14,X15] :
      ( ( ~ v1_relat_2(X14)
        | ~ r2_hidden(X15,k3_relat_1(X14))
        | r2_hidden(k4_tarski(X15,X15),X14)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_1(X14),k3_relat_1(X14))
        | v1_relat_2(X14)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X14),esk2_1(X14)),X14)
        | v1_relat_2(X14)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk5_0,esk5_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_24])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_relat_2(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_18]),c_0_10])])).

cnf(c_0_29,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15]),c_0_10])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t42_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&![X4]:(r2_hidden(X4,k1_wellord1(X3,X1))=>(r2_hidden(k4_tarski(X4,X2),X3)&X4!=X2)))=>r2_hidden(k4_tarski(X1,X2),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_wellord1)).
% 0.13/0.37  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.13/0.37  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.13/0.37  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.13/0.37  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>((((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))&![X4]:(r2_hidden(X4,k1_wellord1(X3,X1))=>(r2_hidden(k4_tarski(X4,X2),X3)&X4!=X2)))=>r2_hidden(k4_tarski(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t42_wellord1])).
% 0.13/0.37  fof(c_0_6, plain, ![X17, X18, X19]:((~v6_relat_2(X17)|(~r2_hidden(X18,k3_relat_1(X17))|~r2_hidden(X19,k3_relat_1(X17))|X18=X19|r2_hidden(k4_tarski(X18,X19),X17)|r2_hidden(k4_tarski(X19,X18),X17))|~v1_relat_1(X17))&(((((r2_hidden(esk3_1(X17),k3_relat_1(X17))|v6_relat_2(X17)|~v1_relat_1(X17))&(r2_hidden(esk4_1(X17),k3_relat_1(X17))|v6_relat_2(X17)|~v1_relat_1(X17)))&(esk3_1(X17)!=esk4_1(X17)|v6_relat_2(X17)|~v1_relat_1(X17)))&(~r2_hidden(k4_tarski(esk3_1(X17),esk4_1(X17)),X17)|v6_relat_2(X17)|~v1_relat_1(X17)))&(~r2_hidden(k4_tarski(esk4_1(X17),esk3_1(X17)),X17)|v6_relat_2(X17)|~v1_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, ![X25]:(v1_relat_1(esk7_0)&((((v2_wellord1(esk7_0)&r2_hidden(esk5_0,k3_relat_1(esk7_0)))&r2_hidden(esk6_0,k3_relat_1(esk7_0)))&((r2_hidden(k4_tarski(X25,esk6_0),esk7_0)|~r2_hidden(X25,k1_wellord1(esk7_0,esk5_0)))&(X25!=esk6_0|~r2_hidden(X25,k1_wellord1(esk7_0,esk5_0)))))&~r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).
% 0.13/0.37  cnf(c_0_8, plain, (X2=X3|r2_hidden(k4_tarski(X2,X3),X1)|r2_hidden(k4_tarski(X3,X2),X1)|~v6_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (r2_hidden(esk6_0,k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  fof(c_0_11, plain, ![X13]:((((((v1_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13))&(v8_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v4_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v6_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v1_wellord1(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(~v1_relat_2(X13)|~v8_relat_2(X13)|~v4_relat_2(X13)|~v6_relat_2(X13)|~v1_wellord1(X13)|v2_wellord1(X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.13/0.37  fof(c_0_12, plain, ![X5, X6, X7, X8, X9, X10, X11]:((((X8!=X6|~r2_hidden(X8,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(X8,X6),X5)|~r2_hidden(X8,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5)))&(X9=X6|~r2_hidden(k4_tarski(X9,X6),X5)|r2_hidden(X9,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5)))&((~r2_hidden(esk1_3(X5,X10,X11),X11)|(esk1_3(X5,X10,X11)=X10|~r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5))|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))&((esk1_3(X5,X10,X11)!=X10|r2_hidden(esk1_3(X5,X10,X11),X11)|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)|r2_hidden(esk1_3(X5,X10,X11),X11)|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (X1=esk6_0|r2_hidden(k4_tarski(esk6_0,X1),esk7_0)|r2_hidden(k4_tarski(X1,esk6_0),esk7_0)|~v6_relat_2(esk7_0)|~r2_hidden(X1,k3_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.13/0.37  cnf(c_0_14, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (v2_wellord1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_16, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (X1=esk6_0|r2_hidden(k4_tarski(X1,esk6_0),esk7_0)|r2_hidden(k4_tarski(esk6_0,X1),esk7_0)|~r2_hidden(X1,k3_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_10])])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(esk5_0,k3_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (~r2_hidden(k4_tarski(esk5_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (X1!=esk6_0|~r2_hidden(X1,k1_wellord1(esk7_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_21, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (esk6_0=esk5_0|r2_hidden(k4_tarski(esk6_0,esk5_0),esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk6_0,k1_wellord1(esk7_0,esk5_0))), inference(er,[status(thm)],[c_0_20])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (esk6_0=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_10])]), c_0_23])).
% 0.13/0.37  fof(c_0_25, plain, ![X14, X15]:((~v1_relat_2(X14)|(~r2_hidden(X15,k3_relat_1(X14))|r2_hidden(k4_tarski(X15,X15),X14))|~v1_relat_1(X14))&((r2_hidden(esk2_1(X14),k3_relat_1(X14))|v1_relat_2(X14)|~v1_relat_1(X14))&(~r2_hidden(k4_tarski(esk2_1(X14),esk2_1(X14)),X14)|v1_relat_2(X14)|~v1_relat_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (~r2_hidden(k4_tarski(esk5_0,esk5_0),esk7_0)), inference(rw,[status(thm)],[c_0_19, c_0_24])).
% 0.13/0.37  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (~v1_relat_2(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_18]), c_0_10])])).
% 0.13/0.37  cnf(c_0_29, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_15]), c_0_10])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 31
% 0.13/0.37  # Proof object clause steps            : 20
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 17
% 0.13/0.37  # Proof object clause conjectures      : 14
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 5
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 18
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 5
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 28
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 28
% 0.13/0.37  # Processed clauses                    : 45
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 3
% 0.13/0.37  # ...remaining for further processing  : 42
% 0.13/0.37  # Other redundant clauses eliminated   : 5
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 8
% 0.13/0.37  # Generated clauses                    : 45
% 0.13/0.37  # ...of the previous two non-trivial   : 44
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 41
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 5
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 29
% 0.13/0.37  #    Positive orientable unit clauses  : 4
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 22
% 0.13/0.37  # Current number of unprocessed clauses: 27
% 0.13/0.37  # ...number of literals in the above   : 124
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 9
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 84
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 34
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 77
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 1
% 0.13/0.37  # BW rewrite match successes           : 1
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 2806
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.031 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.034 s
% 0.13/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
