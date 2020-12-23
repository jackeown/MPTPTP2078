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
% DateTime   : Thu Dec  3 10:48:36 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  42 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 173 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t44_relat_1])).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk2_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk3_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_relat_1(esk10_0)
    & ~ r1_tarski(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X24,X25,X26,X27,X28,X30,X31,X32,X35] :
      ( ( r2_hidden(k4_tarski(X27,esk5_5(X24,X25,X26,X27,X28)),X24)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk5_5(X24,X25,X26,X27,X28),X28),X25)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X30,X32),X24)
        | ~ r2_hidden(k4_tarski(X32,X31),X25)
        | r2_hidden(k4_tarski(X30,X31),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26)),X26)
        | ~ r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X35),X24)
        | ~ r2_hidden(k4_tarski(X35,esk7_3(X24,X25,X26)),X25)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk8_3(X24,X25,X26)),X24)
        | r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk8_3(X24,X25,X26),esk7_3(X24,X25,X26)),X25)
        | r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ v1_relat_1(X38)
      | v1_relat_1(k5_relat_1(X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk5_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),k1_relat_1(k5_relat_1(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,esk5_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),esk2_3(k5_relat_1(esk9_0,esk10_0),k1_relat_1(k5_relat_1(esk9_0,esk10_0)),esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)))),k5_relat_1(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),esk5_5(esk9_0,esk10_0,k5_relat_1(esk9_0,esk10_0),esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),esk2_3(k5_relat_1(esk9_0,esk10_0),k1_relat_1(k5_relat_1(esk9_0,esk10_0)),esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0))))),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),k1_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:23:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.20/0.38  # and selection function SelectCQIArNXTEqFirst.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.028 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t44_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 0.20/0.38  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.20/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))))), inference(assume_negation,[status(cth)],[t44_relat_1])).
% 0.20/0.38  fof(c_0_6, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:(((~r2_hidden(X15,X14)|r2_hidden(k4_tarski(X15,esk2_3(X13,X14,X15)),X13)|X14!=k1_relat_1(X13))&(~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(X17,X14)|X14!=k1_relat_1(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|~r2_hidden(k4_tarski(esk3_2(X19,X20),X22),X19)|X20=k1_relat_1(X19))&(r2_hidden(esk3_2(X19,X20),X20)|r2_hidden(k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)),X19)|X20=k1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.38  fof(c_0_7, negated_conjecture, (v1_relat_1(esk9_0)&(v1_relat_1(esk10_0)&~r1_tarski(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X24, X25, X26, X27, X28, X30, X31, X32, X35]:((((r2_hidden(k4_tarski(X27,esk5_5(X24,X25,X26,X27,X28)),X24)|~r2_hidden(k4_tarski(X27,X28),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk5_5(X24,X25,X26,X27,X28),X28),X25)|~r2_hidden(k4_tarski(X27,X28),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24)))&(~r2_hidden(k4_tarski(X30,X32),X24)|~r2_hidden(k4_tarski(X32,X31),X25)|r2_hidden(k4_tarski(X30,X31),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24)))&((~r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26)),X26)|(~r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X35),X24)|~r2_hidden(k4_tarski(X35,esk7_3(X24,X25,X26)),X25))|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&((r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk8_3(X24,X25,X26)),X24)|r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26)),X26)|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk8_3(X24,X25,X26),esk7_3(X24,X25,X26)),X25)|r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk7_3(X24,X25,X26)),X26)|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X37, X38]:(~v1_relat_1(X37)|~v1_relat_1(X38)|v1_relat_1(k5_relat_1(X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.38  cnf(c_0_11, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (~r1_tarski(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk5_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_15, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),k1_relat_1(k5_relat_1(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,esk5_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_15])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),esk2_3(k5_relat_1(esk9_0,esk10_0),k1_relat_1(k5_relat_1(esk9_0,esk10_0)),esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)))),k5_relat_1(esk9_0,esk10_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_23, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),esk5_5(esk9_0,esk10_0,k5_relat_1(esk9_0,esk10_0),esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),esk2_3(k5_relat_1(esk9_0,esk10_0),k1_relat_1(k5_relat_1(esk9_0,esk10_0)),esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0))))),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(k5_relat_1(esk9_0,esk10_0)),k1_relat_1(esk9_0)),k1_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_12]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 28
% 0.20/0.38  # Proof object clause steps            : 17
% 0.20/0.38  # Proof object formula steps           : 11
% 0.20/0.38  # Proof object conjectures             : 11
% 0.20/0.38  # Proof object clause conjectures      : 8
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 9
% 0.20/0.38  # Proof object initial formulas used   : 5
% 0.20/0.38  # Proof object generating inferences   : 5
% 0.20/0.38  # Proof object simplifying inferences  : 8
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 5
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 17
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 17
% 0.20/0.38  # Processed clauses                    : 69
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 10
% 0.20/0.38  # ...remaining for further processing  : 59
% 0.20/0.38  # Other redundant clauses eliminated   : 5
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 129
% 0.20/0.38  # ...of the previous two non-trivial   : 116
% 0.20/0.38  # Contextual simplify-reflections      : 3
% 0.20/0.38  # Paramodulations                      : 120
% 0.20/0.38  # Factorizations                       : 4
% 0.20/0.38  # Equation resolutions                 : 5
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 36
% 0.20/0.38  #    Positive orientable unit clauses  : 7
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 28
% 0.20/0.38  # Current number of unprocessed clauses: 79
% 0.20/0.38  # ...number of literals in the above   : 348
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 18
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 618
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 215
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.20/0.38  # Unit Clause-clause subsumption calls : 22
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 0
% 0.20/0.39  # BW rewrite match successes           : 0
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 5068
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.033 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.037 s
% 0.20/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
