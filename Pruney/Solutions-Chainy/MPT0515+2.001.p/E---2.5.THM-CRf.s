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
% DateTime   : Thu Dec  3 10:50:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 123 expanded)
%              Number of clauses        :   29 (  57 expanded)
%              Number of leaves         :    4 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 673 expanded)
%              Number of equality atoms :   34 ( 115 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t115_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

fof(c_0_4,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X10,X6)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(X9,X10),X7)
        | ~ r2_hidden(k4_tarski(X9,X10),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(X12,X6)
        | ~ r2_hidden(k4_tarski(X11,X12),X7)
        | r2_hidden(k4_tarski(X11,X12),X8)
        | X8 != k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X6)
        | ~ r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X6)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)
        | X8 = k8_relat_1(X6,X7)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk3_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk4_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk4_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk4_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk5_2(X21,X22),esk4_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_6,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k8_relat_1(X5,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | v1_relat_1(k8_relat_1(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),X4)
    | X1 != k8_relat_1(X5,X4)
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X3,X1),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X5 != k8_relat_1(X2,X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk3_3(k8_relat_1(X1,X2),X3,X4),X4),X2)
    | X3 != k2_relat_1(k8_relat_1(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
        <=> ( r2_hidden(X1,X2)
            & r2_hidden(X1,k2_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_relat_1])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X2)
    | X3 != k8_relat_1(X2,X4)
    | X5 != k2_relat_1(X3)
    | ~ r2_hidden(X1,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),X4)
    | X4 != k8_relat_1(X5,X1)
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X5)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X3 != k2_relat_1(k8_relat_1(X4,X5))
    | X2 != k2_relat_1(X5)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X5) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))
      | ~ r2_hidden(esk6_0,esk7_0)
      | ~ r2_hidden(esk6_0,k2_relat_1(esk8_0)) )
    & ( r2_hidden(esk6_0,esk7_0)
      | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) )
    & ( r2_hidden(esk6_0,k2_relat_1(esk8_0))
      | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | X3 != k2_relat_1(k8_relat_1(X2,X4))
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),k8_relat_1(X4,X1))
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]),c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X4,X3)))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk8_0))
    | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(k8_relat_1(X3,X4))
    | X5 != k2_relat_1(X4)
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X5)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_13,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk8_0))
    | r2_hidden(esk6_0,X1)
    | X1 != k2_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))
    | ~ r2_hidden(esk6_0,esk7_0)
    | ~ r2_hidden(esk6_0,k2_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_24])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))
    | X4 != k2_relat_1(X3)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk8_0)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))
    | ~ r2_hidden(esk6_0,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(k8_relat_1(X1,X2)))
    | k2_relat_1(esk8_0) != k2_relat_1(X2)
    | ~ r2_hidden(esk6_0,X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(k8_relat_1(X1,esk8_0)))
    | ~ r2_hidden(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_24])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 0.19/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.40  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.19/0.40  fof(t115_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_relat_1)).
% 0.19/0.40  fof(c_0_4, plain, ![X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X10,X6)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(X9,X10),X7)|~r2_hidden(k4_tarski(X9,X10),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(X12,X6)|~r2_hidden(k4_tarski(X11,X12),X7)|r2_hidden(k4_tarski(X11,X12),X8)|X8!=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|(~r2_hidden(esk2_3(X6,X7,X8),X6)|~r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7))|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(esk2_3(X6,X7,X8),X6)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),esk2_3(X6,X7,X8)),X8)|X8=k8_relat_1(X6,X7)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.19/0.40  fof(c_0_5, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(esk3_3(X15,X16,X17),X17),X15)|X16!=k2_relat_1(X15))&(~r2_hidden(k4_tarski(X20,X19),X15)|r2_hidden(X19,X16)|X16!=k2_relat_1(X15)))&((~r2_hidden(esk4_2(X21,X22),X22)|~r2_hidden(k4_tarski(X24,esk4_2(X21,X22)),X21)|X22=k2_relat_1(X21))&(r2_hidden(esk4_2(X21,X22),X22)|r2_hidden(k4_tarski(esk5_2(X21,X22),esk4_2(X21,X22)),X21)|X22=k2_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.40  cnf(c_0_6, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),X4)|X4!=k8_relat_1(X5,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_7, plain, (r2_hidden(k4_tarski(esk3_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  fof(c_0_8, plain, ![X26, X27]:(~v1_relat_1(X27)|v1_relat_1(k8_relat_1(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.19/0.40  cnf(c_0_9, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),X4)|X1!=k8_relat_1(X5,X4)|X2!=k2_relat_1(X1)|~r2_hidden(X3,X2)|~v1_relat_1(X1)|~v1_relat_1(X4)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.19/0.40  cnf(c_0_10, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X4!=k8_relat_1(X2,X5)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X3,X1),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X5!=k8_relat_1(X2,X4)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_13, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  cnf(c_0_14, plain, (r2_hidden(k4_tarski(esk3_3(k8_relat_1(X1,X2),X3,X4),X4),X2)|X3!=k2_relat_1(k8_relat_1(X1,X2))|~r2_hidden(X4,X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])).
% 0.19/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k2_relat_1(X3)))))), inference(assume_negation,[status(cth)],[t115_relat_1])).
% 0.19/0.40  cnf(c_0_16, plain, (r2_hidden(X1,X2)|X3!=k8_relat_1(X2,X4)|X5!=k2_relat_1(X3)|~r2_hidden(X1,X5)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_11, c_0_7])).
% 0.19/0.40  cnf(c_0_17, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),X4)|X4!=k8_relat_1(X5,X1)|X2!=k2_relat_1(X1)|~r2_hidden(X3,X5)|~r2_hidden(X3,X2)|~v1_relat_1(X4)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_7])).
% 0.19/0.40  cnf(c_0_18, plain, (r2_hidden(X1,X2)|X3!=k2_relat_1(k8_relat_1(X4,X5))|X2!=k2_relat_1(X5)|~r2_hidden(X1,X3)|~v1_relat_1(X5)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.40  fof(c_0_19, negated_conjecture, (v1_relat_1(esk8_0)&((~r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))|(~r2_hidden(esk6_0,esk7_0)|~r2_hidden(esk6_0,k2_relat_1(esk8_0))))&((r2_hidden(esk6_0,esk7_0)|r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))))&(r2_hidden(esk6_0,k2_relat_1(esk8_0))|r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 0.19/0.40  cnf(c_0_20, plain, (r2_hidden(X1,X2)|X3!=k2_relat_1(k8_relat_1(X2,X4))|~r2_hidden(X1,X3)|~v1_relat_1(X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_10])).
% 0.19/0.40  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X3),k8_relat_1(X4,X1))|X2!=k2_relat_1(X1)|~r2_hidden(X3,X4)|~r2_hidden(X3,X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_17]), c_0_10])).
% 0.19/0.40  cnf(c_0_22, plain, (r2_hidden(X1,X2)|X2!=k2_relat_1(X3)|~r2_hidden(X1,k2_relat_1(k8_relat_1(X4,X3)))|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk8_0))|r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (r2_hidden(esk6_0,esk7_0)|r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_27, plain, (r2_hidden(X1,X2)|X2!=k2_relat_1(k8_relat_1(X3,X4))|X5!=k2_relat_1(X4)|~r2_hidden(X1,X3)|~r2_hidden(X1,X5)|~v1_relat_1(X4)), inference(spm,[status(thm)],[c_0_13, c_0_21])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk8_0))|r2_hidden(esk6_0,X1)|X1!=k2_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.40  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))|~r2_hidden(esk6_0,esk7_0)|~r2_hidden(esk6_0,k2_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (r2_hidden(esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_24])])).
% 0.19/0.40  cnf(c_0_31, plain, (r2_hidden(X1,k2_relat_1(k8_relat_1(X2,X3)))|X4!=k2_relat_1(X3)|~r2_hidden(X1,X2)|~r2_hidden(X1,X4)|~v1_relat_1(X3)), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk8_0))), inference(er,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (~r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))|~r2_hidden(esk6_0,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(k8_relat_1(X1,X2)))|k2_relat_1(esk8_0)!=k2_relat_1(X2)|~r2_hidden(esk6_0,X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (~r2_hidden(esk6_0,k2_relat_1(k8_relat_1(esk7_0,esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_32])])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(k8_relat_1(X1,esk8_0)))|~r2_hidden(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_24])])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 38
% 0.19/0.40  # Proof object clause steps            : 29
% 0.19/0.40  # Proof object formula steps           : 9
% 0.19/0.40  # Proof object conjectures             : 15
% 0.19/0.40  # Proof object clause conjectures      : 12
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 10
% 0.19/0.40  # Proof object initial formulas used   : 4
% 0.19/0.40  # Proof object generating inferences   : 17
% 0.19/0.40  # Proof object simplifying inferences  : 15
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 4
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 15
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 15
% 0.19/0.40  # Processed clauses                    : 200
% 0.19/0.40  # ...of these trivial                  : 21
% 0.19/0.40  # ...subsumed                          : 35
% 0.19/0.40  # ...remaining for further processing  : 144
% 0.19/0.40  # Other redundant clauses eliminated   : 5
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 5
% 0.19/0.40  # Backward-rewritten                   : 24
% 0.19/0.40  # Generated clauses                    : 506
% 0.19/0.40  # ...of the previous two non-trivial   : 458
% 0.19/0.40  # Contextual simplify-reflections      : 14
% 0.19/0.40  # Paramodulations                      : 452
% 0.19/0.40  # Factorizations                       : 8
% 0.19/0.40  # Equation resolutions                 : 46
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 100
% 0.19/0.40  #    Positive orientable unit clauses  : 4
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 94
% 0.19/0.40  # Current number of unprocessed clauses: 278
% 0.19/0.40  # ...number of literals in the above   : 1898
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 44
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 3141
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 620
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 52
% 0.19/0.40  # Unit Clause-clause subsumption calls : 83
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 3
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 14248
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.054 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.059 s
% 0.19/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
