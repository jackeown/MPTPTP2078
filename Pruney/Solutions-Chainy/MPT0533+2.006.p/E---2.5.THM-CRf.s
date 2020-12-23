%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:13 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   36 (  65 expanded)
%              Number of clauses        :   21 (  26 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  139 ( 227 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k4_tarski(X3,X3),X2) )
       => r1_tarski(k6_relat_1(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t133_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ! [X4] :
          ( v1_relat_1(X4)
         => ( ( r1_tarski(X3,X4)
              & r1_tarski(X1,X2) )
           => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(t50_relat_1,axiom,(
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

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(c_0_7,plain,(
    ! [X26,X27] :
      ( ( r2_hidden(esk4_2(X26,X27),X26)
        | r1_tarski(k6_relat_1(X26),X27)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X26,X27),esk4_2(X26,X27)),X27)
        | r1_tarski(k6_relat_1(X26),X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_relat_1])])])])).

fof(c_0_8,plain,(
    ! [X19] : v1_relat_1(k6_relat_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( X13 = X14
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(X15,X11)
        | X15 != X16
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X12)
        | ~ r2_hidden(esk2_2(X11,X12),X11)
        | esk2_2(X11,X12) != esk3_2(X11,X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( esk2_2(X11,X12) = esk3_2(X11,X12)
        | r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(k6_relat_1(X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ! [X4] :
            ( v1_relat_1(X4)
           => ( ( r1_tarski(X3,X4)
                & r1_tarski(X1,X2) )
             => r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t133_relat_1])).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_relat_1(X25)
      | ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k5_relat_1(X22,X24),k5_relat_1(X23,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).

fof(c_0_15,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k8_relat_1(X20,X21) = k5_relat_1(X21,k6_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_2(X1,k6_relat_1(X2)),X1)
    | r1_tarski(k6_relat_1(X1),k6_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(esk7_0,esk8_0)
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r1_tarski(k6_relat_1(X1),X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk4_2(X1,X2)),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])]),c_0_12])])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_2(X1,k6_relat_1(X2)),X3)
    | r1_tarski(k6_relat_1(X1),k6_relat_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(k5_relat_1(X1,X2),k8_relat_1(X3,X4))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k6_relat_1(X3))
    | ~ r1_tarski(X1,X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_12])])).

cnf(c_0_27,plain,
    ( r1_tarski(k6_relat_1(X1),k6_relat_1(X2))
    | ~ r2_hidden(esk4_2(X1,k6_relat_1(X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_12])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,k6_relat_1(X1)),esk6_0)
    | r1_tarski(k6_relat_1(esk5_0),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X3,X4))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k6_relat_1(X1),k6_relat_1(X3))
    | ~ r1_tarski(X2,X4) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_12])])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k6_relat_1(esk5_0),k6_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.40  #
% 0.12/0.40  # Preprocessing time       : 0.029 s
% 0.12/0.40  # Presaturation interreduction done
% 0.12/0.40  
% 0.12/0.40  # Proof found!
% 0.12/0.40  # SZS status Theorem
% 0.12/0.40  # SZS output start CNFRefutation
% 0.12/0.40  fof(t73_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(![X3]:(r2_hidden(X3,X1)=>r2_hidden(k4_tarski(X3,X3),X2))=>r1_tarski(k6_relat_1(X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 0.12/0.40  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.12/0.40  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.12/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.40  fof(t133_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 0.12/0.40  fof(t50_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 0.12/0.40  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.12/0.40  fof(c_0_7, plain, ![X26, X27]:((r2_hidden(esk4_2(X26,X27),X26)|r1_tarski(k6_relat_1(X26),X27)|~v1_relat_1(X27))&(~r2_hidden(k4_tarski(esk4_2(X26,X27),esk4_2(X26,X27)),X27)|r1_tarski(k6_relat_1(X26),X27)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_relat_1])])])])).
% 0.12/0.40  fof(c_0_8, plain, ![X19]:v1_relat_1(k6_relat_1(X19)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.12/0.40  fof(c_0_9, plain, ![X11, X12, X13, X14, X15, X16]:((((r2_hidden(X13,X11)|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k6_relat_1(X11)|~v1_relat_1(X12))&(X13=X14|~r2_hidden(k4_tarski(X13,X14),X12)|X12!=k6_relat_1(X11)|~v1_relat_1(X12)))&(~r2_hidden(X15,X11)|X15!=X16|r2_hidden(k4_tarski(X15,X16),X12)|X12!=k6_relat_1(X11)|~v1_relat_1(X12)))&((~r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X12)|(~r2_hidden(esk2_2(X11,X12),X11)|esk2_2(X11,X12)!=esk3_2(X11,X12))|X12=k6_relat_1(X11)|~v1_relat_1(X12))&((r2_hidden(esk2_2(X11,X12),X11)|r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X12)|X12=k6_relat_1(X11)|~v1_relat_1(X12))&(esk2_2(X11,X12)=esk3_2(X11,X12)|r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X12)|X12=k6_relat_1(X11)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.12/0.40  fof(c_0_10, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.40  cnf(c_0_11, plain, (r2_hidden(esk4_2(X1,X2),X1)|r1_tarski(k6_relat_1(X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.40  cnf(c_0_12, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X3,X4)&r1_tarski(X1,X2))=>r1_tarski(k8_relat_1(X1,X3),k8_relat_1(X2,X4)))))), inference(assume_negation,[status(cth)],[t133_relat_1])).
% 0.12/0.40  fof(c_0_14, plain, ![X22, X23, X24, X25]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~v1_relat_1(X24)|(~v1_relat_1(X25)|(~r1_tarski(X22,X23)|~r1_tarski(X24,X25)|r1_tarski(k5_relat_1(X22,X24),k5_relat_1(X23,X25))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).
% 0.12/0.40  fof(c_0_15, plain, ![X20, X21]:(~v1_relat_1(X21)|k8_relat_1(X20,X21)=k5_relat_1(X21,k6_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.12/0.40  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)|X1!=X3|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.40  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.40  cnf(c_0_18, plain, (r2_hidden(esk4_2(X1,k6_relat_1(X2)),X1)|r1_tarski(k6_relat_1(X1),k6_relat_1(X2))), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.40  fof(c_0_19, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&((r1_tarski(esk7_0,esk8_0)&r1_tarski(esk5_0,esk6_0))&~r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.12/0.40  cnf(c_0_20, plain, (r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.40  cnf(c_0_21, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.40  cnf(c_0_22, plain, (r1_tarski(k6_relat_1(X1),X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),esk4_2(X1,X2)),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.40  cnf(c_0_23, plain, (r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])]), c_0_12])])).
% 0.12/0.40  cnf(c_0_24, plain, (r2_hidden(esk4_2(X1,k6_relat_1(X2)),X3)|r1_tarski(k6_relat_1(X1),k6_relat_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.40  cnf(c_0_25, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.40  cnf(c_0_26, plain, (r1_tarski(k5_relat_1(X1,X2),k8_relat_1(X3,X4))|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X2,k6_relat_1(X3))|~r1_tarski(X1,X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_12])])).
% 0.12/0.40  cnf(c_0_27, plain, (r1_tarski(k6_relat_1(X1),k6_relat_1(X2))|~r2_hidden(esk4_2(X1,k6_relat_1(X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_12])])).
% 0.12/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_2(esk5_0,k6_relat_1(X1)),esk6_0)|r1_tarski(k6_relat_1(esk5_0),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.40  cnf(c_0_29, negated_conjecture, (~r1_tarski(k8_relat_1(esk5_0,esk7_0),k8_relat_1(esk6_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.40  cnf(c_0_30, plain, (r1_tarski(k8_relat_1(X1,X2),k8_relat_1(X3,X4))|~v1_relat_1(X4)|~v1_relat_1(X2)|~r1_tarski(k6_relat_1(X1),k6_relat_1(X3))|~r1_tarski(X2,X4)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_12])])).
% 0.12/0.40  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.40  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.40  cnf(c_0_33, negated_conjecture, (r1_tarski(k6_relat_1(esk5_0),k6_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.40  cnf(c_0_34, negated_conjecture, (r1_tarski(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.40  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])]), ['proof']).
% 0.12/0.40  # SZS output end CNFRefutation
% 0.12/0.40  # Proof object total steps             : 36
% 0.12/0.40  # Proof object clause steps            : 21
% 0.12/0.40  # Proof object formula steps           : 15
% 0.12/0.40  # Proof object conjectures             : 11
% 0.12/0.40  # Proof object clause conjectures      : 8
% 0.12/0.40  # Proof object formula conjectures     : 3
% 0.12/0.40  # Proof object initial clauses used    : 12
% 0.12/0.40  # Proof object initial formulas used   : 7
% 0.12/0.40  # Proof object generating inferences   : 8
% 0.12/0.40  # Proof object simplifying inferences  : 15
% 0.12/0.40  # Training examples: 0 positive, 0 negative
% 0.12/0.40  # Parsed axioms                        : 7
% 0.12/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.40  # Initial clauses                      : 19
% 0.12/0.40  # Removed in clause preprocessing      : 0
% 0.12/0.40  # Initial clauses in saturation        : 19
% 0.12/0.40  # Processed clauses                    : 325
% 0.12/0.40  # ...of these trivial                  : 0
% 0.12/0.40  # ...subsumed                          : 75
% 0.12/0.40  # ...remaining for further processing  : 250
% 0.12/0.40  # Other redundant clauses eliminated   : 4
% 0.12/0.40  # Clauses deleted for lack of memory   : 0
% 0.12/0.40  # Backward-subsumed                    : 7
% 0.12/0.40  # Backward-rewritten                   : 0
% 0.12/0.40  # Generated clauses                    : 680
% 0.12/0.40  # ...of the previous two non-trivial   : 663
% 0.12/0.40  # Contextual simplify-reflections      : 4
% 0.12/0.40  # Paramodulations                      : 677
% 0.12/0.40  # Factorizations                       : 0
% 0.12/0.40  # Equation resolutions                 : 4
% 0.12/0.40  # Propositional unsat checks           : 0
% 0.12/0.40  #    Propositional check models        : 0
% 0.12/0.40  #    Propositional check unsatisfiable : 0
% 0.12/0.40  #    Propositional clauses             : 0
% 0.12/0.40  #    Propositional clauses after purity: 0
% 0.12/0.40  #    Propositional unsat core size     : 0
% 0.12/0.40  #    Propositional preprocessing time  : 0.000
% 0.12/0.40  #    Propositional encoding time       : 0.000
% 0.12/0.40  #    Propositional solver time         : 0.000
% 0.12/0.40  #    Success case prop preproc time    : 0.000
% 0.12/0.40  #    Success case prop encoding time   : 0.000
% 0.12/0.40  #    Success case prop solver time     : 0.000
% 0.12/0.40  # Current number of processed clauses  : 221
% 0.12/0.40  #    Positive orientable unit clauses  : 12
% 0.12/0.40  #    Positive unorientable unit clauses: 0
% 0.12/0.40  #    Negative unit clauses             : 1
% 0.12/0.40  #    Non-unit-clauses                  : 208
% 0.12/0.40  # Current number of unprocessed clauses: 365
% 0.12/0.40  # ...number of literals in the above   : 1985
% 0.12/0.40  # Current number of archived formulas  : 0
% 0.12/0.40  # Current number of archived clauses   : 26
% 0.12/0.40  # Clause-clause subsumption calls (NU) : 21847
% 0.12/0.40  # Rec. Clause-clause subsumption calls : 7054
% 0.12/0.40  # Non-unit clause-clause subsumptions  : 86
% 0.12/0.40  # Unit Clause-clause subsumption calls : 82
% 0.12/0.40  # Rewrite failures with RHS unbound    : 0
% 0.12/0.40  # BW rewrite match attempts            : 6
% 0.12/0.40  # BW rewrite match successes           : 0
% 0.12/0.40  # Condensation attempts                : 0
% 0.12/0.40  # Condensation successes               : 0
% 0.12/0.40  # Termbank termtop insertions          : 18409
% 0.12/0.40  
% 0.12/0.40  # -------------------------------------------------
% 0.12/0.40  # User time                : 0.059 s
% 0.12/0.40  # System time              : 0.007 s
% 0.12/0.40  # Total time               : 0.067 s
% 0.12/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
