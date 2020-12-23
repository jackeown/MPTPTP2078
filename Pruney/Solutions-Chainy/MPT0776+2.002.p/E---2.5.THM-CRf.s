%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:46 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 378 expanded)
%              Number of clauses        :   36 ( 170 expanded)
%              Number of leaves         :    5 (  87 expanded)
%              Depth                    :   18
%              Number of atoms          :  136 (1396 expanded)
%              Number of equality atoms :   29 ( 257 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_2(X2)
       => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_wellord1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( v4_relat_2(X2)
         => v4_relat_2(k2_wellord1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t25_wellord1])).

fof(c_0_6,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | k2_wellord1(X22,X23) = k3_xboole_0(X22,k2_zfmisc_1(X23,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v4_relat_2(esk8_0)
    & ~ v4_relat_2(k2_wellord1(esk8_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X24,X25,X26] :
      ( ( ~ v4_relat_2(X24)
        | ~ r2_hidden(k4_tarski(X25,X26),X24)
        | ~ r2_hidden(k4_tarski(X26,X25),X24)
        | X25 = X26
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk5_1(X24),esk6_1(X24)),X24)
        | v4_relat_2(X24)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk6_1(X24),esk5_1(X24)),X24)
        | v4_relat_2(X24)
        | ~ v1_relat_1(X24) )
      & ( esk5_1(X24) != esk6_1(X24)
        | v4_relat_2(X24)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

fof(c_0_10,plain,(
    ! [X14,X15,X18,X20,X21] :
      ( ( ~ v1_relat_1(X14)
        | ~ r2_hidden(X15,X14)
        | X15 = k4_tarski(esk2_2(X14,X15),esk3_2(X14,X15)) )
      & ( r2_hidden(esk4_1(X18),X18)
        | v1_relat_1(X18) )
      & ( esk4_1(X18) != k4_tarski(X20,X21)
        | v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k3_xboole_0(esk8_0,k2_zfmisc_1(X1,X1)) = k2_wellord1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v4_relat_2(k2_wellord1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v4_relat_2(X1)
    | r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk6_1(X1),esk5_1(X1)),X1)
    | v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X2 = X3
    | ~ v4_relat_2(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( v4_relat_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,k2_wellord1(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0))
    | r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( v4_relat_2(X1)
    | r2_hidden(k4_tarski(esk6_1(X1),esk5_1(X1)),X1)
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X2,X1),esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_13])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)
    | r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0))
    | r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( esk6_1(k2_wellord1(esk8_0,esk7_0)) = esk5_1(k2_wellord1(esk8_0,esk7_0))
    | r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))
    | ~ r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)
    | r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_28])).

cnf(c_0_31,plain,
    ( v4_relat_2(X1)
    | esk5_1(X1) != esk6_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( esk6_1(k2_wellord1(esk8_0,esk7_0)) = esk5_1(k2_wellord1(esk8_0,esk7_0))
    | r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18]),c_0_15])).

cnf(c_0_34,plain,
    ( X2 = k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | esk4_1(X1) != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( k4_tarski(esk2_2(esk8_0,esk4_1(k2_wellord1(esk8_0,esk7_0))),esk3_2(esk8_0,esk4_1(k2_wellord1(esk8_0,esk7_0)))) = esk4_1(k2_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_13])])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(X1)
    | esk4_1(X1) != esk4_1(k2_wellord1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk8_0,esk7_0)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_39]),c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_39]),c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( esk6_1(k2_wellord1(esk8_0,esk7_0)) = esk5_1(k2_wellord1(esk8_0,esk7_0))
    | ~ r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( esk6_1(k2_wellord1(esk8_0,esk7_0)) = esk5_1(k2_wellord1(esk8_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_39])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.69/0.84  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EA
% 0.69/0.84  # and selection function SelectDivPreferIntoLits.
% 0.69/0.84  #
% 0.69/0.84  # Preprocessing time       : 0.028 s
% 0.69/0.84  # Presaturation interreduction done
% 0.69/0.84  
% 0.69/0.84  # Proof found!
% 0.69/0.84  # SZS status Theorem
% 0.69/0.84  # SZS output start CNFRefutation
% 0.69/0.84  fof(t25_wellord1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_2(X2)=>v4_relat_2(k2_wellord1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_wellord1)).
% 0.69/0.84  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.69/0.84  fof(d6_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 0.69/0.84  fof(l3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>![X2, X3]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X2),X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_wellord1)).
% 0.69/0.84  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.69/0.84  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(v4_relat_2(X2)=>v4_relat_2(k2_wellord1(X2,X1))))), inference(assume_negation,[status(cth)],[t25_wellord1])).
% 0.69/0.84  fof(c_0_6, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.69/0.84  fof(c_0_7, plain, ![X22, X23]:(~v1_relat_1(X22)|k2_wellord1(X22,X23)=k3_xboole_0(X22,k2_zfmisc_1(X23,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).
% 0.69/0.84  fof(c_0_8, negated_conjecture, (v1_relat_1(esk8_0)&(v4_relat_2(esk8_0)&~v4_relat_2(k2_wellord1(esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.69/0.84  fof(c_0_9, plain, ![X24, X25, X26]:((~v4_relat_2(X24)|(~r2_hidden(k4_tarski(X25,X26),X24)|~r2_hidden(k4_tarski(X26,X25),X24)|X25=X26)|~v1_relat_1(X24))&(((r2_hidden(k4_tarski(esk5_1(X24),esk6_1(X24)),X24)|v4_relat_2(X24)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk6_1(X24),esk5_1(X24)),X24)|v4_relat_2(X24)|~v1_relat_1(X24)))&(esk5_1(X24)!=esk6_1(X24)|v4_relat_2(X24)|~v1_relat_1(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).
% 0.69/0.84  fof(c_0_10, plain, ![X14, X15, X18, X20, X21]:((~v1_relat_1(X14)|(~r2_hidden(X15,X14)|X15=k4_tarski(esk2_2(X14,X15),esk3_2(X14,X15))))&((r2_hidden(esk4_1(X18),X18)|v1_relat_1(X18))&(esk4_1(X18)!=k4_tarski(X20,X21)|v1_relat_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.69/0.84  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.69/0.84  cnf(c_0_12, plain, (k2_wellord1(X1,X2)=k3_xboole_0(X1,k2_zfmisc_1(X2,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.69/0.84  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.69/0.84  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)|v4_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.69/0.84  cnf(c_0_15, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.69/0.84  cnf(c_0_16, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_11])).
% 0.69/0.84  cnf(c_0_17, negated_conjecture, (k3_xboole_0(esk8_0,k2_zfmisc_1(X1,X1))=k2_wellord1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.69/0.84  cnf(c_0_18, negated_conjecture, (~v4_relat_2(k2_wellord1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.69/0.84  cnf(c_0_19, plain, (v4_relat_2(X1)|r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)|r2_hidden(esk4_1(X1),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.69/0.84  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk6_1(X1),esk5_1(X1)),X1)|v4_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.69/0.84  cnf(c_0_21, plain, (X2=X3|~v4_relat_2(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r2_hidden(k4_tarski(X3,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.69/0.84  cnf(c_0_22, negated_conjecture, (v4_relat_2(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.69/0.84  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,k2_wellord1(esk8_0,X2))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.69/0.84  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0))|r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.69/0.84  cnf(c_0_25, plain, (v4_relat_2(X1)|r2_hidden(k4_tarski(esk6_1(X1),esk5_1(X1)),X1)|r2_hidden(esk4_1(X1),X1)), inference(spm,[status(thm)],[c_0_20, c_0_15])).
% 0.69/0.84  cnf(c_0_26, negated_conjecture, (X1=X2|~r2_hidden(k4_tarski(X2,X1),esk8_0)|~r2_hidden(k4_tarski(X1,X2),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_13])])).
% 0.69/0.84  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)|r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.69/0.84  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0))|r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_18, c_0_25])).
% 0.69/0.84  cnf(c_0_29, negated_conjecture, (esk6_1(k2_wellord1(esk8_0,esk7_0))=esk5_1(k2_wellord1(esk8_0,esk7_0))|r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))|~r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.69/0.84  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)|r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_23, c_0_28])).
% 0.69/0.84  cnf(c_0_31, plain, (v4_relat_2(X1)|esk5_1(X1)!=esk6_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.69/0.84  cnf(c_0_32, negated_conjecture, (esk6_1(k2_wellord1(esk8_0,esk7_0))=esk5_1(k2_wellord1(esk8_0,esk7_0))|r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.69/0.84  cnf(c_0_33, negated_conjecture, (r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),k2_wellord1(esk8_0,esk7_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_18]), c_0_15])).
% 0.69/0.84  cnf(c_0_34, plain, (X2=k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.69/0.84  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_1(k2_wellord1(esk8_0,esk7_0)),esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.69/0.84  cnf(c_0_36, plain, (v1_relat_1(X1)|esk4_1(X1)!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.69/0.84  cnf(c_0_37, negated_conjecture, (k4_tarski(esk2_2(esk8_0,esk4_1(k2_wellord1(esk8_0,esk7_0))),esk3_2(esk8_0,esk4_1(k2_wellord1(esk8_0,esk7_0))))=esk4_1(k2_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_13])])).
% 0.69/0.84  cnf(c_0_38, negated_conjecture, (v1_relat_1(X1)|esk4_1(X1)!=esk4_1(k2_wellord1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.69/0.84  cnf(c_0_39, negated_conjecture, (v1_relat_1(k2_wellord1(esk8_0,esk7_0))), inference(er,[status(thm)],[c_0_38])).
% 0.69/0.84  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_39]), c_0_18])).
% 0.69/0.84  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk5_1(k2_wellord1(esk8_0,esk7_0)),esk6_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_40])).
% 0.69/0.84  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),k2_wellord1(esk8_0,esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_39]), c_0_18])).
% 0.69/0.84  cnf(c_0_43, negated_conjecture, (esk6_1(k2_wellord1(esk8_0,esk7_0))=esk5_1(k2_wellord1(esk8_0,esk7_0))|~r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_41])).
% 0.69/0.84  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk6_1(k2_wellord1(esk8_0,esk7_0)),esk5_1(k2_wellord1(esk8_0,esk7_0))),esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_42])).
% 0.69/0.84  cnf(c_0_45, negated_conjecture, (esk6_1(k2_wellord1(esk8_0,esk7_0))=esk5_1(k2_wellord1(esk8_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.69/0.84  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_45]), c_0_39])]), c_0_18]), ['proof']).
% 0.69/0.84  # SZS output end CNFRefutation
% 0.69/0.84  # Proof object total steps             : 47
% 0.69/0.84  # Proof object clause steps            : 36
% 0.69/0.84  # Proof object formula steps           : 11
% 0.69/0.84  # Proof object conjectures             : 27
% 0.69/0.84  # Proof object clause conjectures      : 24
% 0.69/0.84  # Proof object formula conjectures     : 3
% 0.69/0.84  # Proof object initial clauses used    : 12
% 0.69/0.84  # Proof object initial formulas used   : 5
% 0.69/0.84  # Proof object generating inferences   : 22
% 0.69/0.84  # Proof object simplifying inferences  : 14
% 0.69/0.84  # Training examples: 0 positive, 0 negative
% 0.69/0.84  # Parsed axioms                        : 5
% 0.69/0.84  # Removed by relevancy pruning/SinE    : 0
% 0.69/0.84  # Initial clauses                      : 17
% 0.69/0.84  # Removed in clause preprocessing      : 0
% 0.69/0.84  # Initial clauses in saturation        : 17
% 0.69/0.84  # Processed clauses                    : 361
% 0.69/0.84  # ...of these trivial                  : 4
% 0.69/0.84  # ...subsumed                          : 3
% 0.69/0.84  # ...remaining for further processing  : 354
% 0.69/0.84  # Other redundant clauses eliminated   : 78
% 0.69/0.84  # Clauses deleted for lack of memory   : 0
% 0.69/0.84  # Backward-subsumed                    : 1
% 0.69/0.84  # Backward-rewritten                   : 20
% 0.69/0.84  # Generated clauses                    : 40015
% 0.69/0.84  # ...of the previous two non-trivial   : 39371
% 0.69/0.84  # Contextual simplify-reflections      : 3
% 0.69/0.84  # Paramodulations                      : 39936
% 0.69/0.84  # Factorizations                       : 0
% 0.69/0.84  # Equation resolutions                 : 79
% 0.69/0.84  # Propositional unsat checks           : 0
% 0.69/0.84  #    Propositional check models        : 0
% 0.69/0.84  #    Propositional check unsatisfiable : 0
% 0.69/0.84  #    Propositional clauses             : 0
% 0.69/0.84  #    Propositional clauses after purity: 0
% 0.69/0.84  #    Propositional unsat core size     : 0
% 0.69/0.84  #    Propositional preprocessing time  : 0.000
% 0.69/0.84  #    Propositional encoding time       : 0.000
% 0.69/0.84  #    Propositional solver time         : 0.000
% 0.69/0.84  #    Success case prop preproc time    : 0.000
% 0.69/0.84  #    Success case prop encoding time   : 0.000
% 0.69/0.84  #    Success case prop solver time     : 0.000
% 0.69/0.84  # Current number of processed clauses  : 313
% 0.69/0.84  #    Positive orientable unit clauses  : 163
% 0.69/0.84  #    Positive unorientable unit clauses: 0
% 0.69/0.84  #    Negative unit clauses             : 1
% 0.69/0.84  #    Non-unit-clauses                  : 149
% 0.69/0.84  # Current number of unprocessed clauses: 39037
% 0.69/0.84  # ...number of literals in the above   : 126197
% 0.69/0.84  # Current number of archived formulas  : 0
% 0.69/0.84  # Current number of archived clauses   : 38
% 0.69/0.84  # Clause-clause subsumption calls (NU) : 5965
% 0.69/0.84  # Rec. Clause-clause subsumption calls : 4962
% 0.69/0.84  # Non-unit clause-clause subsumptions  : 7
% 0.69/0.84  # Unit Clause-clause subsumption calls : 3215
% 0.69/0.84  # Rewrite failures with RHS unbound    : 0
% 0.69/0.84  # BW rewrite match attempts            : 1605
% 0.69/0.84  # BW rewrite match successes           : 5
% 0.69/0.84  # Condensation attempts                : 0
% 0.69/0.84  # Condensation successes               : 0
% 0.69/0.84  # Termbank termtop insertions          : 887563
% 0.69/0.85  
% 0.69/0.85  # -------------------------------------------------
% 0.69/0.85  # User time                : 0.478 s
% 0.69/0.85  # System time              : 0.024 s
% 0.69/0.85  # Total time               : 0.502 s
% 0.69/0.85  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
