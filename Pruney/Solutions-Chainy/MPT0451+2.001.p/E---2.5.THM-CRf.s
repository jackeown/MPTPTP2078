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
% DateTime   : Thu Dec  3 10:48:35 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 275 expanded)
%              Number of clauses        :   34 ( 134 expanded)
%              Number of leaves         :    5 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  161 (1206 expanded)
%              Number of equality atoms :   42 ( 344 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
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

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t37_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(c_0_5,plain,(
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

fof(c_0_6,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(k4_tarski(X29,X30),X28)
        | r2_hidden(k4_tarski(X30,X29),X27)
        | X28 != k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X32,X31),X27)
        | r2_hidden(k4_tarski(X31,X32),X28)
        | X28 != k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)
        | ~ r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)
        | X28 = k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)
        | r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)
        | X28 = k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_7,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | v1_relat_1(k4_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_8,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

fof(c_0_13,plain,(
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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t37_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k4_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k2_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k2_relat_1(esk9_0) != k1_relat_1(k4_relat_1(esk9_0))
      | k1_relat_1(esk9_0) != k2_relat_1(k4_relat_1(esk9_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),k4_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = k1_relat_1(X2)
    | r2_hidden(esk2_2(X2,X1),k2_relat_1(k4_relat_1(X2)))
    | r2_hidden(esk2_2(X2,X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(k4_relat_1(X2),k2_relat_1(k4_relat_1(X2)),X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(k4_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k1_relat_1(esk9_0)
    | r2_hidden(esk2_2(esk9_0,X1),k2_relat_1(k4_relat_1(esk9_0)))
    | r2_hidden(esk2_2(esk9_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_31,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk2_2(X2,X1),k2_relat_1(k4_relat_1(X2)))
    | ~ r2_hidden(esk2_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk9_0)) = k1_relat_1(esk9_0)
    | r2_hidden(esk2_2(esk9_0,k2_relat_1(k4_relat_1(esk9_0))),k2_relat_1(k4_relat_1(esk9_0))) ),
    inference(ef,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,esk1_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk5_2(X2,X1),k1_relat_1(k4_relat_1(X2)))
    | r2_hidden(esk5_2(X2,X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk9_0) != k1_relat_1(k4_relat_1(esk9_0))
    | k1_relat_1(esk9_0) != k2_relat_1(k4_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk9_0)) = k1_relat_1(esk9_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24])]),c_0_33])).

cnf(c_0_38,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk5_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(esk1_3(k4_relat_1(X1),k1_relat_1(k4_relat_1(X1)),X2),X2),X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k4_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k2_relat_1(esk9_0)
    | r2_hidden(esk5_2(esk9_0,X1),k1_relat_1(k4_relat_1(esk9_0)))
    | r2_hidden(esk5_2(esk9_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk9_0)) != k2_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_42,plain,
    ( X1 = k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk5_2(X2,X1),k1_relat_1(k4_relat_1(X2)))
    | ~ r2_hidden(esk5_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_2(esk9_0,k1_relat_1(k4_relat_1(esk9_0))),k1_relat_1(k4_relat_1(esk9_0))) ),
    inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_40]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_24]),c_0_43])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:06:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.88/1.04  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.88/1.04  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.88/1.04  #
% 0.88/1.04  # Preprocessing time       : 0.013 s
% 0.88/1.04  # Presaturation interreduction done
% 0.88/1.04  
% 0.88/1.04  # Proof found!
% 0.88/1.04  # SZS status Theorem
% 0.88/1.04  # SZS output start CNFRefutation
% 0.88/1.04  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.88/1.04  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 0.88/1.04  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.88/1.04  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.88/1.04  fof(t37_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.88/1.04  fof(c_0_5, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X18),X16)|X17!=k2_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)))&((~r2_hidden(esk5_2(X22,X23),X23)|~r2_hidden(k4_tarski(X25,esk5_2(X22,X23)),X22)|X23=k2_relat_1(X22))&(r2_hidden(esk5_2(X22,X23),X23)|r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)|X23=k2_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.88/1.04  fof(c_0_6, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(k4_tarski(X29,X30),X28)|r2_hidden(k4_tarski(X30,X29),X27)|X28!=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27))&(~r2_hidden(k4_tarski(X32,X31),X27)|r2_hidden(k4_tarski(X31,X32),X28)|X28!=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27)))&((~r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)|~r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)|X28=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)|r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)|X28=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 0.88/1.04  fof(c_0_7, plain, ![X35]:(~v1_relat_1(X35)|v1_relat_1(k4_relat_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.88/1.04  cnf(c_0_8, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.88/1.04  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k4_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.88/1.04  cnf(c_0_10, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.88/1.04  cnf(c_0_11, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_8])).
% 0.88/1.04  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])).
% 0.88/1.04  fof(c_0_13, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)|X6!=k1_relat_1(X5))&(~r2_hidden(k4_tarski(X9,X10),X5)|r2_hidden(X9,X6)|X6!=k1_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)|X12=k1_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)|X12=k1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.88/1.04  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))))), inference(assume_negation,[status(cth)],[t37_relat_1])).
% 0.88/1.04  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X3!=k4_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.88/1.04  cnf(c_0_16, plain, (r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.88/1.04  cnf(c_0_17, plain, (r2_hidden(X1,k2_relat_1(k4_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.88/1.04  cnf(c_0_18, plain, (r2_hidden(esk2_2(X1,X2),X2)|r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.04  fof(c_0_19, negated_conjecture, (v1_relat_1(esk9_0)&(k2_relat_1(esk9_0)!=k1_relat_1(k4_relat_1(esk9_0))|k1_relat_1(esk9_0)!=k2_relat_1(k4_relat_1(esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.88/1.04  cnf(c_0_20, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.04  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X2,X1),k4_relat_1(X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_10])).
% 0.88/1.04  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_16])).
% 0.88/1.04  cnf(c_0_23, plain, (X1=k1_relat_1(X2)|r2_hidden(esk2_2(X2,X1),k2_relat_1(k4_relat_1(X2)))|r2_hidden(esk2_2(X2,X1),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.88/1.04  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.88/1.04  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_20])).
% 0.88/1.04  cnf(c_0_26, plain, (X2=k1_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),X3),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.04  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,esk4_3(k4_relat_1(X2),k2_relat_1(k4_relat_1(X2)),X1)),X2)|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(k4_relat_1(X2)))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.88/1.04  cnf(c_0_28, negated_conjecture, (X1=k1_relat_1(esk9_0)|r2_hidden(esk2_2(esk9_0,X1),k2_relat_1(k4_relat_1(esk9_0)))|r2_hidden(esk2_2(esk9_0,X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.88/1.04  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,esk1_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.88/1.04  cnf(c_0_30, plain, (r2_hidden(X1,k1_relat_1(k4_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_12])).
% 0.88/1.04  cnf(c_0_31, plain, (r2_hidden(esk5_2(X1,X2),X2)|r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.88/1.04  cnf(c_0_32, plain, (X1=k1_relat_1(X2)|~v1_relat_1(X2)|~r2_hidden(esk2_2(X2,X1),k2_relat_1(k4_relat_1(X2)))|~r2_hidden(esk2_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.88/1.04  cnf(c_0_33, negated_conjecture, (k2_relat_1(k4_relat_1(esk9_0))=k1_relat_1(esk9_0)|r2_hidden(esk2_2(esk9_0,k2_relat_1(k4_relat_1(esk9_0))),k2_relat_1(k4_relat_1(esk9_0)))), inference(ef,[status(thm)],[c_0_28])).
% 0.88/1.04  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,esk1_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 0.88/1.04  cnf(c_0_35, plain, (X1=k2_relat_1(X2)|r2_hidden(esk5_2(X2,X1),k1_relat_1(k4_relat_1(X2)))|r2_hidden(esk5_2(X2,X1),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.88/1.04  cnf(c_0_36, negated_conjecture, (k2_relat_1(esk9_0)!=k1_relat_1(k4_relat_1(esk9_0))|k1_relat_1(esk9_0)!=k2_relat_1(k4_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.88/1.04  cnf(c_0_37, negated_conjecture, (k2_relat_1(k4_relat_1(esk9_0))=k1_relat_1(esk9_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_24])]), c_0_33])).
% 0.88/1.04  cnf(c_0_38, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk5_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk5_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.88/1.04  cnf(c_0_39, plain, (r2_hidden(k4_tarski(esk1_3(k4_relat_1(X1),k1_relat_1(k4_relat_1(X1)),X2),X2),X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(k4_relat_1(X1)))), inference(spm,[status(thm)],[c_0_21, c_0_34])).
% 0.88/1.04  cnf(c_0_40, negated_conjecture, (X1=k2_relat_1(esk9_0)|r2_hidden(esk5_2(esk9_0,X1),k1_relat_1(k4_relat_1(esk9_0)))|r2_hidden(esk5_2(esk9_0,X1),X1)), inference(spm,[status(thm)],[c_0_35, c_0_24])).
% 0.88/1.04  cnf(c_0_41, negated_conjecture, (k1_relat_1(k4_relat_1(esk9_0))!=k2_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.88/1.04  cnf(c_0_42, plain, (X1=k2_relat_1(X2)|~v1_relat_1(X2)|~r2_hidden(esk5_2(X2,X1),k1_relat_1(k4_relat_1(X2)))|~r2_hidden(esk5_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.88/1.04  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_2(esk9_0,k1_relat_1(k4_relat_1(esk9_0))),k1_relat_1(k4_relat_1(esk9_0)))), inference(sr,[status(thm)],[inference(ef,[status(thm)],[c_0_40]), c_0_41])).
% 0.88/1.04  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_24]), c_0_43])]), c_0_41]), ['proof']).
% 0.88/1.04  # SZS output end CNFRefutation
% 0.88/1.04  # Proof object total steps             : 45
% 0.88/1.04  # Proof object clause steps            : 34
% 0.88/1.04  # Proof object formula steps           : 11
% 0.88/1.04  # Proof object conjectures             : 12
% 0.88/1.04  # Proof object clause conjectures      : 9
% 0.88/1.04  # Proof object formula conjectures     : 3
% 0.88/1.04  # Proof object initial clauses used    : 13
% 0.88/1.04  # Proof object initial formulas used   : 5
% 0.88/1.04  # Proof object generating inferences   : 14
% 0.88/1.04  # Proof object simplifying inferences  : 18
% 0.88/1.04  # Training examples: 0 positive, 0 negative
% 0.88/1.04  # Parsed axioms                        : 5
% 0.88/1.04  # Removed by relevancy pruning/SinE    : 0
% 0.88/1.04  # Initial clauses                      : 15
% 0.88/1.04  # Removed in clause preprocessing      : 0
% 0.88/1.04  # Initial clauses in saturation        : 15
% 0.88/1.04  # Processed clauses                    : 2923
% 0.88/1.04  # ...of these trivial                  : 0
% 0.88/1.04  # ...subsumed                          : 1152
% 0.88/1.04  # ...remaining for further processing  : 1771
% 0.88/1.04  # Other redundant clauses eliminated   : 6
% 0.88/1.04  # Clauses deleted for lack of memory   : 0
% 0.88/1.04  # Backward-subsumed                    : 151
% 0.88/1.04  # Backward-rewritten                   : 3
% 0.88/1.04  # Generated clauses                    : 58162
% 0.88/1.04  # ...of the previous two non-trivial   : 58060
% 0.88/1.04  # Contextual simplify-reflections      : 24
% 0.88/1.04  # Paramodulations                      : 58148
% 0.88/1.04  # Factorizations                       : 8
% 0.88/1.04  # Equation resolutions                 : 6
% 0.88/1.04  # Propositional unsat checks           : 0
% 0.88/1.04  #    Propositional check models        : 0
% 0.88/1.04  #    Propositional check unsatisfiable : 0
% 0.88/1.04  #    Propositional clauses             : 0
% 0.88/1.04  #    Propositional clauses after purity: 0
% 0.88/1.04  #    Propositional unsat core size     : 0
% 0.88/1.04  #    Propositional preprocessing time  : 0.000
% 0.88/1.04  #    Propositional encoding time       : 0.000
% 0.88/1.04  #    Propositional solver time         : 0.000
% 0.88/1.04  #    Success case prop preproc time    : 0.000
% 0.88/1.04  #    Success case prop encoding time   : 0.000
% 0.88/1.04  #    Success case prop solver time     : 0.000
% 0.88/1.04  # Current number of processed clauses  : 1596
% 0.88/1.04  #    Positive orientable unit clauses  : 3
% 0.88/1.04  #    Positive unorientable unit clauses: 0
% 0.88/1.04  #    Negative unit clauses             : 1
% 0.88/1.04  #    Non-unit-clauses                  : 1592
% 0.88/1.04  # Current number of unprocessed clauses: 55089
% 0.88/1.04  # ...number of literals in the above   : 249224
% 0.88/1.04  # Current number of archived formulas  : 0
% 0.88/1.04  # Current number of archived clauses   : 169
% 0.88/1.04  # Clause-clause subsumption calls (NU) : 594290
% 0.88/1.04  # Rec. Clause-clause subsumption calls : 377633
% 0.88/1.04  # Non-unit clause-clause subsumptions  : 1327
% 0.88/1.04  # Unit Clause-clause subsumption calls : 192
% 0.88/1.04  # Rewrite failures with RHS unbound    : 0
% 0.88/1.04  # BW rewrite match attempts            : 1
% 0.88/1.04  # BW rewrite match successes           : 1
% 0.88/1.04  # Condensation attempts                : 0
% 0.88/1.04  # Condensation successes               : 0
% 0.88/1.04  # Termbank termtop insertions          : 2038865
% 0.88/1.04  
% 0.88/1.04  # -------------------------------------------------
% 0.88/1.04  # User time                : 0.680 s
% 0.88/1.04  # System time              : 0.029 s
% 0.88/1.04  # Total time               : 0.709 s
% 0.88/1.04  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
