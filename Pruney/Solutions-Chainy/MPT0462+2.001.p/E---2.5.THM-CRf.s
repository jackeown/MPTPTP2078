%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 (  89 expanded)
%              Number of clauses        :   26 (  34 expanded)
%              Number of leaves         :    4 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 543 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(t50_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ! [X4] :
                  ( v1_relat_1(X4)
                 => ( ( r1_tarski(X1,X2)
                      & r1_tarski(X3,X4) )
                   => r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

fof(c_0_4,plain,(
    ! [X14,X15,X16,X17,X18,X20,X21,X22,X25] :
      ( ( r2_hidden(k4_tarski(X17,esk3_5(X14,X15,X16,X17,X18)),X14)
        | ~ r2_hidden(k4_tarski(X17,X18),X16)
        | X16 != k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk3_5(X14,X15,X16,X17,X18),X18),X15)
        | ~ r2_hidden(k4_tarski(X17,X18),X16)
        | X16 != k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X20,X22),X14)
        | ~ r2_hidden(k4_tarski(X22,X21),X15)
        | r2_hidden(k4_tarski(X20,X21),X16)
        | X16 != k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk5_3(X14,X15,X16)),X16)
        | ~ r2_hidden(k4_tarski(esk4_3(X14,X15,X16),X25),X14)
        | ~ r2_hidden(k4_tarski(X25,esk5_3(X14,X15,X16)),X15)
        | X16 = k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk6_3(X14,X15,X16)),X14)
        | r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk5_3(X14,X15,X16)),X16)
        | X16 = k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk6_3(X14,X15,X16),esk5_3(X14,X15,X16)),X15)
        | r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk5_3(X14,X15,X16)),X16)
        | X16 = k5_relat_1(X14,X15)
        | ~ v1_relat_1(X16)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_5,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v1_relat_1(X28)
      | v1_relat_1(k5_relat_1(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(k4_tarski(X9,X10),X7)
        | r2_hidden(k4_tarski(X9,X10),X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X7)
        | r1_tarski(X7,X11)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X11)
        | r1_tarski(X7,X11)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ! [X4] :
                    ( v1_relat_1(X4)
                   => ( ( r1_tarski(X1,X2)
                        & r1_tarski(X3,X4) )
                     => r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_relat_1])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_7]),c_0_8])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & v1_relat_1(esk9_0)
    & v1_relat_1(esk10_0)
    & r1_tarski(esk7_0,esk8_0)
    & r1_tarski(esk9_0,esk10_0)
    & ~ r1_tarski(k5_relat_1(esk7_0,esk9_0),k5_relat_1(esk8_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X5)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ r1_tarski(X2,X5)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_5(X1,esk9_0,k5_relat_1(X1,esk9_0),X2,X3),X3),esk10_0)
    | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,esk9_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X5)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ r1_tarski(X2,X5)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,esk10_0))
    | ~ r2_hidden(k4_tarski(X1,esk3_5(X4,esk9_0,k5_relat_1(X4,esk9_0),X5,X2)),X3)
    | ~ r2_hidden(k4_tarski(X5,X2),k5_relat_1(X4,esk9_0))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk3_5(esk7_0,X2,k5_relat_1(esk7_0,X2),X1,X3)),esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X3),k5_relat_1(esk7_0,X2))
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(esk8_0,esk10_0))
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(esk7_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_24]),c_0_17])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk7_0,esk9_0),X1),esk2_2(k5_relat_1(esk7_0,esk9_0),X1)),k5_relat_1(esk8_0,esk10_0))
    | r1_tarski(k5_relat_1(esk7_0,esk9_0),X1)
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk7_0,esk9_0),k5_relat_1(esk8_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk7_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_8]),c_0_17]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.027 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.19/0.40  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.40  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.19/0.40  fof(t50_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 0.19/0.40  fof(c_0_4, plain, ![X14, X15, X16, X17, X18, X20, X21, X22, X25]:((((r2_hidden(k4_tarski(X17,esk3_5(X14,X15,X16,X17,X18)),X14)|~r2_hidden(k4_tarski(X17,X18),X16)|X16!=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk3_5(X14,X15,X16,X17,X18),X18),X15)|~r2_hidden(k4_tarski(X17,X18),X16)|X16!=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14)))&(~r2_hidden(k4_tarski(X20,X22),X14)|~r2_hidden(k4_tarski(X22,X21),X15)|r2_hidden(k4_tarski(X20,X21),X16)|X16!=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14)))&((~r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk5_3(X14,X15,X16)),X16)|(~r2_hidden(k4_tarski(esk4_3(X14,X15,X16),X25),X14)|~r2_hidden(k4_tarski(X25,esk5_3(X14,X15,X16)),X15))|X16=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))&((r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk6_3(X14,X15,X16)),X14)|r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk5_3(X14,X15,X16)),X16)|X16=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk6_3(X14,X15,X16),esk5_3(X14,X15,X16)),X15)|r2_hidden(k4_tarski(esk4_3(X14,X15,X16),esk5_3(X14,X15,X16)),X16)|X16=k5_relat_1(X14,X15)|~v1_relat_1(X16)|~v1_relat_1(X15)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.19/0.40  fof(c_0_5, plain, ![X27, X28]:(~v1_relat_1(X27)|~v1_relat_1(X28)|v1_relat_1(k5_relat_1(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.40  fof(c_0_6, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(k4_tarski(X9,X10),X7)|r2_hidden(k4_tarski(X9,X10),X8))|~v1_relat_1(X7))&((r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X7)|r1_tarski(X7,X11)|~v1_relat_1(X7))&(~r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X11)|r1_tarski(X7,X11)|~v1_relat_1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.19/0.40  cnf(c_0_7, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_8, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  fof(c_0_9, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4)))))))), inference(assume_negation,[status(cth)],[t50_relat_1])).
% 0.19/0.40  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_11, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_7]), c_0_8])).
% 0.19/0.40  fof(c_0_12, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&(v1_relat_1(esk9_0)&(v1_relat_1(esk10_0)&((r1_tarski(esk7_0,esk8_0)&r1_tarski(esk9_0,esk10_0))&~r1_tarski(k5_relat_1(esk7_0,esk9_0),k5_relat_1(esk8_0,esk10_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.40  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_15, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X5)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))|~r1_tarski(X2,X5)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.40  cnf(c_0_16, negated_conjecture, (r1_tarski(esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_8])).
% 0.19/0.40  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_8])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk3_5(X1,esk9_0,k5_relat_1(X1,esk9_0),X2,X3),X3),esk10_0)|~r2_hidden(k4_tarski(X2,X3),k5_relat_1(X1,esk9_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.19/0.40  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X5)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))|~r1_tarski(X2,X5)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_10, c_0_18])).
% 0.19/0.40  cnf(c_0_23, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,esk10_0))|~r2_hidden(k4_tarski(X1,esk3_5(X4,esk9_0,k5_relat_1(X4,esk9_0),X5,X2)),X3)|~r2_hidden(k4_tarski(X5,X2),k5_relat_1(X4,esk9_0))|~v1_relat_1(X3)|~v1_relat_1(X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.19/0.40  cnf(c_0_26, negated_conjecture, (r2_hidden(k4_tarski(X1,esk3_5(esk7_0,X2,k5_relat_1(esk7_0,X2),X1,X3)),esk8_0)|~r2_hidden(k4_tarski(X1,X3),k5_relat_1(esk7_0,X2))|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.40  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(esk8_0,esk10_0))|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(esk7_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_24]), c_0_17])])).
% 0.19/0.40  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k5_relat_1(esk7_0,esk9_0),X1),esk2_2(k5_relat_1(esk7_0,esk9_0),X1)),k5_relat_1(esk8_0,esk10_0))|r1_tarski(k5_relat_1(esk7_0,esk9_0),X1)|~v1_relat_1(k5_relat_1(esk7_0,esk9_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (~r1_tarski(k5_relat_1(esk7_0,esk9_0),k5_relat_1(esk8_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (~v1_relat_1(k5_relat_1(esk7_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_8]), c_0_17]), c_0_24])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 35
% 0.19/0.40  # Proof object clause steps            : 26
% 0.19/0.40  # Proof object formula steps           : 9
% 0.19/0.40  # Proof object conjectures             : 17
% 0.19/0.40  # Proof object clause conjectures      : 14
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 14
% 0.19/0.40  # Proof object initial formulas used   : 4
% 0.19/0.40  # Proof object generating inferences   : 9
% 0.19/0.40  # Proof object simplifying inferences  : 20
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 4
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 17
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 17
% 0.19/0.40  # Processed clauses                    : 179
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 35
% 0.19/0.40  # ...remaining for further processing  : 144
% 0.19/0.40  # Other redundant clauses eliminated   : 3
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 6
% 0.19/0.40  # Backward-rewritten                   : 0
% 0.19/0.40  # Generated clauses                    : 493
% 0.19/0.40  # ...of the previous two non-trivial   : 489
% 0.19/0.40  # Contextual simplify-reflections      : 5
% 0.19/0.40  # Paramodulations                      : 490
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 3
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
% 0.19/0.40  # Current number of processed clauses  : 118
% 0.19/0.40  #    Positive orientable unit clauses  : 6
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 2
% 0.19/0.40  #    Non-unit-clauses                  : 110
% 0.19/0.40  # Current number of unprocessed clauses: 344
% 0.19/0.40  # ...number of literals in the above   : 2361
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 23
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 5471
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 887
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 46
% 0.19/0.40  # Unit Clause-clause subsumption calls : 74
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 0
% 0.19/0.40  # BW rewrite match successes           : 0
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 18206
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.052 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.058 s
% 0.19/0.40  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
