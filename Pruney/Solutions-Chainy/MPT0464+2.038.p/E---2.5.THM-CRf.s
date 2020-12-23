%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:42 EST 2020

% Result     : Theorem 0.52s
% Output     : CNFRefutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 214 expanded)
%              Number of clauses        :   31 ( 101 expanded)
%              Number of leaves         :    9 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 438 expanded)
%              Number of equality atoms :   15 (  82 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

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

fof(fc1_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t52_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(c_0_9,plain,(
    ! [X17,X18,X19] : r1_tarski(k2_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X19)),k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k2_xboole_0(X15,X16)) = k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | r1_tarski(X9,k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_12,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_13,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X12,X13] : k2_xboole_0(X12,k3_xboole_0(X12,X13)) = X12 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ v1_relat_1(X22)
      | ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_relat_1(X25)
      | ~ r1_tarski(X22,X23)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k5_relat_1(X22,X24),k5_relat_1(X23,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).

fof(c_0_21,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k3_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).

fof(c_0_22,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v1_relat_1(k3_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_relat_1])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X4,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

fof(c_0_33,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_30])])).

cnf(c_0_35,plain,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_32]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(esk3_0,X2)),k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k5_relat_1(X1,k3_xboole_0(esk2_0,X2)),k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_38]),c_0_24])])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k5_relat_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k5_relat_1(esk1_0,esk3_0)))
    | ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk2_0)),k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.52/0.69  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.52/0.69  # and selection function SelectComplexG.
% 0.52/0.69  #
% 0.52/0.69  # Preprocessing time       : 0.027 s
% 0.52/0.69  
% 0.52/0.69  # Proof found!
% 0.52/0.69  # SZS status Theorem
% 0.52/0.69  # SZS output start CNFRefutation
% 0.52/0.69  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.52/0.69  fof(t23_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 0.52/0.69  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.52/0.69  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.52/0.69  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 0.52/0.69  fof(t50_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>![X4]:(v1_relat_1(X4)=>((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 0.52/0.69  fof(fc1_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 0.52/0.69  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.52/0.69  fof(t52_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 0.52/0.69  fof(c_0_9, plain, ![X17, X18, X19]:r1_tarski(k2_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X19)),k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.52/0.69  fof(c_0_10, plain, ![X14, X15, X16]:k3_xboole_0(X14,k2_xboole_0(X15,X16))=k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)), inference(variable_rename,[status(thm)],[t23_xboole_1])).
% 0.52/0.69  fof(c_0_11, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|r1_tarski(X9,k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.52/0.69  fof(c_0_12, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.52/0.69  cnf(c_0_13, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.52/0.69  cnf(c_0_14, plain, (k3_xboole_0(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.52/0.69  fof(c_0_15, plain, ![X12, X13]:k2_xboole_0(X12,k3_xboole_0(X12,X13))=X12, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 0.52/0.69  cnf(c_0_16, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.52/0.69  cnf(c_0_17, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.52/0.69  cnf(c_0_18, plain, (r1_tarski(k3_xboole_0(X1,k2_xboole_0(X2,X3)),k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.52/0.69  cnf(c_0_19, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.52/0.69  fof(c_0_20, plain, ![X22, X23, X24, X25]:(~v1_relat_1(X22)|(~v1_relat_1(X23)|(~v1_relat_1(X24)|(~v1_relat_1(X25)|(~r1_tarski(X22,X23)|~r1_tarski(X24,X25)|r1_tarski(k5_relat_1(X22,X24),k5_relat_1(X23,X25))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_relat_1])])])).
% 0.52/0.69  fof(c_0_21, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k3_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_relat_1])])).
% 0.52/0.69  fof(c_0_22, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.52/0.69  cnf(c_0_23, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X3,X1))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.52/0.69  cnf(c_0_24, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.52/0.69  cnf(c_0_25, plain, (r1_tarski(k5_relat_1(X1,X3),k5_relat_1(X2,X4))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X4)|~r1_tarski(X1,X2)|~r1_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.52/0.69  cnf(c_0_26, plain, (v1_relat_1(k3_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.52/0.69  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.69  fof(c_0_28, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k5_relat_1(X1,X2),k5_relat_1(X1,X3))))))), inference(assume_negation,[status(cth)],[t52_relat_1])).
% 0.52/0.69  cnf(c_0_29, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.52/0.69  cnf(c_0_30, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.52/0.69  cnf(c_0_31, plain, (r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X4,X2))|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X1)|~r1_tarski(X1,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_26])).
% 0.52/0.69  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 0.52/0.69  fof(c_0_33, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.52/0.69  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_30])])).
% 0.52/0.69  cnf(c_0_35, plain, (r1_tarski(k5_relat_1(X1,k3_xboole_0(X2,X3)),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.52/0.69  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.52/0.69  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.52/0.69  cnf(c_0_38, plain, (r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_32]), c_0_34])).
% 0.52/0.69  cnf(c_0_39, negated_conjecture, (r1_tarski(k5_relat_1(X1,k3_xboole_0(esk3_0,X2)),k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.52/0.69  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.52/0.70  cnf(c_0_41, negated_conjecture, (r1_tarski(k5_relat_1(X1,k3_xboole_0(esk2_0,X2)),k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 0.52/0.70  cnf(c_0_42, plain, (k3_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_38]), c_0_24])])).
% 0.52/0.70  cnf(c_0_43, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k5_relat_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.52/0.70  cnf(c_0_44, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,X1)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.52/0.70  cnf(c_0_45, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.52/0.70  cnf(c_0_46, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),k3_xboole_0(X2,k5_relat_1(esk1_0,esk3_0)))|~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk3_0,X1)),X2)), inference(spm,[status(thm)],[c_0_16, c_0_43])).
% 0.52/0.70  cnf(c_0_47, negated_conjecture, (r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(X1,esk2_0)),k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.52/0.70  cnf(c_0_48, negated_conjecture, (~r1_tarski(k5_relat_1(esk1_0,k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k5_relat_1(esk1_0,esk2_0),k5_relat_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.52/0.70  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_34]), c_0_48]), ['proof']).
% 0.52/0.70  # SZS output end CNFRefutation
% 0.52/0.70  # Proof object total steps             : 50
% 0.52/0.70  # Proof object clause steps            : 31
% 0.52/0.70  # Proof object formula steps           : 19
% 0.52/0.70  # Proof object conjectures             : 14
% 0.52/0.70  # Proof object clause conjectures      : 11
% 0.52/0.70  # Proof object formula conjectures     : 3
% 0.52/0.70  # Proof object initial clauses used    : 13
% 0.52/0.70  # Proof object initial formulas used   : 9
% 0.52/0.70  # Proof object generating inferences   : 16
% 0.52/0.70  # Proof object simplifying inferences  : 10
% 0.52/0.70  # Training examples: 0 positive, 0 negative
% 0.52/0.70  # Parsed axioms                        : 9
% 0.52/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.52/0.70  # Initial clauses                      : 14
% 0.52/0.70  # Removed in clause preprocessing      : 0
% 0.52/0.70  # Initial clauses in saturation        : 14
% 0.52/0.70  # Processed clauses                    : 2043
% 0.52/0.70  # ...of these trivial                  : 528
% 0.52/0.70  # ...subsumed                          : 714
% 0.52/0.70  # ...remaining for further processing  : 801
% 0.52/0.70  # Other redundant clauses eliminated   : 2
% 0.52/0.70  # Clauses deleted for lack of memory   : 0
% 0.52/0.70  # Backward-subsumed                    : 30
% 0.52/0.70  # Backward-rewritten                   : 63
% 0.52/0.70  # Generated clauses                    : 42776
% 0.52/0.70  # ...of the previous two non-trivial   : 32632
% 0.52/0.70  # Contextual simplify-reflections      : 6
% 0.52/0.70  # Paramodulations                      : 42774
% 0.52/0.70  # Factorizations                       : 0
% 0.52/0.70  # Equation resolutions                 : 2
% 0.52/0.70  # Propositional unsat checks           : 0
% 0.52/0.70  #    Propositional check models        : 0
% 0.52/0.70  #    Propositional check unsatisfiable : 0
% 0.52/0.70  #    Propositional clauses             : 0
% 0.52/0.70  #    Propositional clauses after purity: 0
% 0.52/0.70  #    Propositional unsat core size     : 0
% 0.52/0.70  #    Propositional preprocessing time  : 0.000
% 0.52/0.70  #    Propositional encoding time       : 0.000
% 0.52/0.70  #    Propositional solver time         : 0.000
% 0.52/0.70  #    Success case prop preproc time    : 0.000
% 0.52/0.70  #    Success case prop encoding time   : 0.000
% 0.52/0.70  #    Success case prop solver time     : 0.000
% 0.52/0.70  # Current number of processed clauses  : 706
% 0.52/0.70  #    Positive orientable unit clauses  : 344
% 0.52/0.70  #    Positive unorientable unit clauses: 1
% 0.52/0.70  #    Negative unit clauses             : 1
% 0.52/0.70  #    Non-unit-clauses                  : 360
% 0.52/0.70  # Current number of unprocessed clauses: 30435
% 0.52/0.70  # ...number of literals in the above   : 57964
% 0.52/0.70  # Current number of archived formulas  : 0
% 0.52/0.70  # Current number of archived clauses   : 93
% 0.52/0.70  # Clause-clause subsumption calls (NU) : 13514
% 0.52/0.70  # Rec. Clause-clause subsumption calls : 10721
% 0.52/0.70  # Non-unit clause-clause subsumptions  : 731
% 0.52/0.70  # Unit Clause-clause subsumption calls : 124
% 0.52/0.70  # Rewrite failures with RHS unbound    : 0
% 0.52/0.70  # BW rewrite match attempts            : 2774
% 0.52/0.70  # BW rewrite match successes           : 101
% 0.52/0.70  # Condensation attempts                : 0
% 0.52/0.70  # Condensation successes               : 0
% 0.52/0.70  # Termbank termtop insertions          : 841215
% 0.52/0.70  
% 0.52/0.70  # -------------------------------------------------
% 0.52/0.70  # User time                : 0.320 s
% 0.52/0.70  # System time              : 0.024 s
% 0.52/0.70  # Total time               : 0.345 s
% 0.52/0.70  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
