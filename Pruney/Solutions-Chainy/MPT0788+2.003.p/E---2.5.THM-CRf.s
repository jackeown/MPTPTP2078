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
% DateTime   : Thu Dec  3 10:56:57 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 249 expanded)
%              Number of clauses        :   24 (  84 expanded)
%              Number of leaves         :    5 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 (1658 expanded)
%              Number of equality atoms :   26 ( 272 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_wellord1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
        <=> ( X1 = X2
            | r2_hidden(X1,k1_wellord1(X3,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(t37_wellord1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( v2_wellord1(X3)
          & r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) )
       => ( r2_hidden(k4_tarski(X1,X2),X3)
        <=> r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( ( v2_wellord1(X3)
            & r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) )
         => ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
          <=> ( X1 = X2
              | r2_hidden(X1,k1_wellord1(X3,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_wellord1])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v2_wellord1(esk5_0)
    & r2_hidden(esk3_0,k3_relat_1(esk5_0))
    & r2_hidden(esk4_0,k3_relat_1(esk5_0))
    & ( esk3_0 != esk4_0
      | ~ r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0)) )
    & ( ~ r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))
      | ~ r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0)) )
    & ( r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0))
      | esk3_0 = esk4_0
      | r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(k4_tarski(X17,X18),X19)
        | r1_tarski(k1_wellord1(X19,X17),k1_wellord1(X19,X18))
        | ~ v2_wellord1(X19)
        | ~ r2_hidden(X17,k3_relat_1(X19))
        | ~ r2_hidden(X18,k3_relat_1(X19))
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(k1_wellord1(X19,X17),k1_wellord1(X19,X18))
        | r2_hidden(k4_tarski(X17,X18),X19)
        | ~ v2_wellord1(X19)
        | ~ r2_hidden(X17,k3_relat_1(X19))
        | ~ r2_hidden(X18,k3_relat_1(X19))
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_wellord1])])])).

fof(c_0_8,plain,(
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

cnf(c_0_9,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))
    | ~ r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v2_wellord1(X3)
    | ~ r2_hidden(X1,k3_relat_1(X3))
    | ~ r2_hidden(X2,k3_relat_1(X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v2_wellord1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk4_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk3_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))
    | ~ v2_wellord1(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ r2_hidden(X3,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0))
    | esk3_0 = esk4_0
    | r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))
    | ~ r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( X1 = X2
    | r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))
    | r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14])])).

cnf(c_0_23,negated_conjecture,
    ( esk3_0 != esk4_0
    | ~ r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( X1 = X2
    | r2_hidden(X1,k1_wellord1(X3,X2))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(sr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( esk4_0 != esk3_0
    | ~ r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_14])]),c_0_22])).

fof(c_0_28,plain,(
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

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk3_0,esk3_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_27])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_31,plain,(
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

cnf(c_0_32,negated_conjecture,
    ( ~ v1_relat_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13]),c_0_14])])).

cnf(c_0_33,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_11]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:24:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.017 s
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(t38_wellord1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))<=>(X1=X2|r2_hidden(X1,k1_wellord1(X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_wellord1)).
% 0.12/0.36  fof(t37_wellord1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 0.12/0.36  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 0.12/0.36  fof(l1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>![X2]:(r2_hidden(X2,k3_relat_1(X1))=>r2_hidden(k4_tarski(X2,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_wellord1)).
% 0.12/0.36  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.12/0.36  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(((v2_wellord1(X3)&r2_hidden(X1,k3_relat_1(X3)))&r2_hidden(X2,k3_relat_1(X3)))=>(r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))<=>(X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))))))), inference(assume_negation,[status(cth)],[t38_wellord1])).
% 0.12/0.36  fof(c_0_6, negated_conjecture, (v1_relat_1(esk5_0)&(((v2_wellord1(esk5_0)&r2_hidden(esk3_0,k3_relat_1(esk5_0)))&r2_hidden(esk4_0,k3_relat_1(esk5_0)))&(((esk3_0!=esk4_0|~r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0)))&(~r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))|~r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0))))&(r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0))|(esk3_0=esk4_0|r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.12/0.36  fof(c_0_7, plain, ![X17, X18, X19]:((~r2_hidden(k4_tarski(X17,X18),X19)|r1_tarski(k1_wellord1(X19,X17),k1_wellord1(X19,X18))|(~v2_wellord1(X19)|~r2_hidden(X17,k3_relat_1(X19))|~r2_hidden(X18,k3_relat_1(X19)))|~v1_relat_1(X19))&(~r1_tarski(k1_wellord1(X19,X17),k1_wellord1(X19,X18))|r2_hidden(k4_tarski(X17,X18),X19)|(~v2_wellord1(X19)|~r2_hidden(X17,k3_relat_1(X19))|~r2_hidden(X18,k3_relat_1(X19)))|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_wellord1])])])).
% 0.12/0.36  fof(c_0_8, plain, ![X5, X6, X7, X8, X9, X10, X11]:((((X8!=X6|~r2_hidden(X8,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(X8,X6),X5)|~r2_hidden(X8,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5)))&(X9=X6|~r2_hidden(k4_tarski(X9,X6),X5)|r2_hidden(X9,X7)|X7!=k1_wellord1(X5,X6)|~v1_relat_1(X5)))&((~r2_hidden(esk1_3(X5,X10,X11),X11)|(esk1_3(X5,X10,X11)=X10|~r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5))|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))&((esk1_3(X5,X10,X11)!=X10|r2_hidden(esk1_3(X5,X10,X11),X11)|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(esk1_3(X5,X10,X11),X10),X5)|r2_hidden(esk1_3(X5,X10,X11),X11)|X11=k1_wellord1(X5,X10)|~v1_relat_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.12/0.36  cnf(c_0_9, negated_conjecture, (~r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))|~r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_10, plain, (r1_tarski(k1_wellord1(X3,X1),k1_wellord1(X3,X2))|~r2_hidden(k4_tarski(X1,X2),X3)|~v2_wellord1(X3)|~r2_hidden(X1,k3_relat_1(X3))|~r2_hidden(X2,k3_relat_1(X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_11, negated_conjecture, (v2_wellord1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_12, negated_conjecture, (r2_hidden(esk4_0,k3_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_13, negated_conjecture, (r2_hidden(esk3_0,k3_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X2,X3),X1)|~r1_tarski(k1_wellord1(X1,X2),k1_wellord1(X1,X3))|~v2_wellord1(X1)|~r2_hidden(X2,k3_relat_1(X1))|~r2_hidden(X3,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_17, negated_conjecture, (r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0))|esk3_0=esk4_0|r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_18, negated_conjecture, (~r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))|~r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])])).
% 0.12/0.36  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,k1_wellord1(X3,X2))|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_20, plain, (X1=X2|r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_21, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))|r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11]), c_0_12]), c_0_13]), c_0_14])])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk3_0,k1_wellord1(esk5_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_14])])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (esk3_0!=esk4_0|~r1_tarski(k1_wellord1(esk5_0,esk3_0),k1_wellord1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_24, plain, (X1=X2|r2_hidden(X1,k1_wellord1(X3,X2))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (esk4_0=esk3_0|r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0)), inference(sr,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (esk4_0!=esk3_0|~r2_hidden(k4_tarski(esk3_0,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])])).
% 0.12/0.36  cnf(c_0_27, negated_conjecture, (esk4_0=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_14])]), c_0_22])).
% 0.12/0.36  fof(c_0_28, plain, ![X14, X15]:((~v1_relat_2(X14)|(~r2_hidden(X15,k3_relat_1(X14))|r2_hidden(k4_tarski(X15,X15),X14))|~v1_relat_1(X14))&((r2_hidden(esk2_1(X14),k3_relat_1(X14))|v1_relat_2(X14)|~v1_relat_1(X14))&(~r2_hidden(k4_tarski(esk2_1(X14),esk2_1(X14)),X14)|v1_relat_2(X14)|~v1_relat_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (~r2_hidden(k4_tarski(esk3_0,esk3_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_27])])).
% 0.12/0.36  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X2,X2),X1)|~v1_relat_2(X1)|~r2_hidden(X2,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.36  fof(c_0_31, plain, ![X13]:((((((v1_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13))&(v8_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v4_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v6_relat_2(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(v1_wellord1(X13)|~v2_wellord1(X13)|~v1_relat_1(X13)))&(~v1_relat_2(X13)|~v8_relat_2(X13)|~v4_relat_2(X13)|~v6_relat_2(X13)|~v1_wellord1(X13)|v2_wellord1(X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (~v1_relat_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_13]), c_0_14])])).
% 0.12/0.36  cnf(c_0_33, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_11]), c_0_14])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 35
% 0.12/0.36  # Proof object clause steps            : 24
% 0.12/0.36  # Proof object formula steps           : 11
% 0.12/0.36  # Proof object conjectures             : 19
% 0.12/0.36  # Proof object clause conjectures      : 16
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 13
% 0.12/0.36  # Proof object initial formulas used   : 5
% 0.12/0.36  # Proof object generating inferences   : 7
% 0.12/0.36  # Proof object simplifying inferences  : 32
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 5
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 24
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 24
% 0.12/0.36  # Processed clauses                    : 43
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 5
% 0.12/0.36  # ...remaining for further processing  : 38
% 0.12/0.36  # Other redundant clauses eliminated   : 4
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 8
% 0.12/0.36  # Generated clauses                    : 34
% 0.12/0.36  # ...of the previous two non-trivial   : 28
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 29
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 4
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 25
% 0.12/0.36  #    Positive orientable unit clauses  : 4
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 3
% 0.12/0.36  #    Non-unit-clauses                  : 18
% 0.12/0.36  # Current number of unprocessed clauses: 9
% 0.12/0.36  # ...number of literals in the above   : 27
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 10
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 310
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 122
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.36  # Unit Clause-clause subsumption calls : 5
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 2251
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.017 s
% 0.12/0.36  # System time              : 0.004 s
% 0.12/0.36  # Total time               : 0.021 s
% 0.12/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
