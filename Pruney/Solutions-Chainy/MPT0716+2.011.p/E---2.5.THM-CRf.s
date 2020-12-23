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
% DateTime   : Thu Dec  3 10:55:44 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 204 expanded)
%              Number of clauses        :   31 (  75 expanded)
%              Number of leaves         :    9 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  169 (1110 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   19 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
            <=> ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
              <=> ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t171_funct_1])).

fof(c_0_10,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
      | ~ r1_tarski(esk4_0,k1_relat_1(esk2_0))
      | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) )
    & ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
      | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) )
    & ( r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
      | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))
        | ~ r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))
        | r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ r1_tarski(X22,k1_relat_1(X24))
      | ~ r1_tarski(k9_relat_1(X24,X22),X23)
      | r1_tarski(X22,k10_relat_1(X24,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk4_0,k10_relat_1(esk2_0,X1))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20]),c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v1_relat_1(X19)
      | k1_relat_1(k5_relat_1(X18,X19)) = k10_relat_1(X18,k1_relat_1(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_31,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ r1_tarski(X15,X16)
      | r1_tarski(k9_relat_1(X17,X15),k9_relat_1(X17,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | r1_tarski(esk4_0,k10_relat_1(esk2_0,k1_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_34,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | k2_xboole_0(X13,X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_21]),c_0_22])])).

fof(c_0_37,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(k2_xboole_0(X10,X11),X12)
      | r1_tarski(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_40,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | r1_tarski(k9_relat_1(X21,k10_relat_1(X21,X20)),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k2_xboole_0(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))) = k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k9_relat_1(X1,esk4_0),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),k1_relat_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_36])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_22]),c_0_20]),c_0_21])]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.21/0.41  # and selection function SelectNewComplexAHP.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.027 s
% 0.21/0.41  # Presaturation interreduction done
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 0.21/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.41  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.21/0.41  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.21/0.41  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.21/0.41  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.21/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.41  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.21/0.41  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.21/0.41  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.21/0.41  fof(c_0_10, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.41  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|(~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))))&((r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))&(r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.21/0.41  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_13, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  fof(c_0_14, plain, ![X25, X26, X27]:(((r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))|~r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26))))&(~r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))|r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.21/0.41  cnf(c_0_15, negated_conjecture, (r2_hidden(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.41  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_17, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_18, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.21/0.41  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  fof(c_0_23, plain, ![X22, X23, X24]:(~v1_relat_1(X24)|~v1_funct_1(X24)|(~r1_tarski(X22,k1_relat_1(X24))|~r1_tarski(k9_relat_1(X24,X22),X23)|r1_tarski(X22,k10_relat_1(X24,X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.21/0.41  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.21/0.41  cnf(c_0_26, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.41  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (r1_tarski(esk4_0,k10_relat_1(esk2_0,X1))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_20]), c_0_22])])).
% 0.21/0.41  cnf(c_0_29, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  fof(c_0_30, plain, ![X18, X19]:(~v1_relat_1(X18)|(~v1_relat_1(X19)|k1_relat_1(k5_relat_1(X18,X19))=k10_relat_1(X18,k1_relat_1(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.21/0.41  fof(c_0_31, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|(~r1_tarski(X15,X16)|r1_tarski(k9_relat_1(X17,X15),k9_relat_1(X17,X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.21/0.41  cnf(c_0_32, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|r1_tarski(esk4_0,k10_relat_1(esk2_0,k1_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.41  cnf(c_0_33, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.41  fof(c_0_34, plain, ![X13, X14]:(~r1_tarski(X13,X14)|k2_xboole_0(X13,X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.41  cnf(c_0_35, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_21]), c_0_22])])).
% 0.21/0.41  fof(c_0_37, plain, ![X10, X11, X12]:(~r1_tarski(k2_xboole_0(X10,X11),X12)|r1_tarski(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.21/0.41  cnf(c_0_38, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.41  cnf(c_0_39, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.41  fof(c_0_40, plain, ![X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|r1_tarski(k9_relat_1(X21,k10_relat_1(X21,X20)),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.21/0.41  cnf(c_0_41, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_42, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.41  cnf(c_0_43, negated_conjecture, (k2_xboole_0(k9_relat_1(X1,esk4_0),k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))=k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.41  cnf(c_0_44, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.41  cnf(c_0_45, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27])])).
% 0.21/0.41  cnf(c_0_46, negated_conjecture, (r1_tarski(k9_relat_1(X1,esk4_0),X2)|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0))),X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.21/0.41  cnf(c_0_47, plain, (r1_tarski(k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))),k1_relat_1(X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_44, c_0_33])).
% 0.21/0.41  cnf(c_0_48, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_36])])).
% 0.21/0.41  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_22]), c_0_20]), c_0_21])]), c_0_48]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 50
% 0.21/0.41  # Proof object clause steps            : 31
% 0.21/0.41  # Proof object formula steps           : 19
% 0.21/0.41  # Proof object conjectures             : 23
% 0.21/0.41  # Proof object clause conjectures      : 20
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 17
% 0.21/0.41  # Proof object initial formulas used   : 9
% 0.21/0.41  # Proof object generating inferences   : 12
% 0.21/0.41  # Proof object simplifying inferences  : 20
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 9
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 19
% 0.21/0.41  # Removed in clause preprocessing      : 0
% 0.21/0.41  # Initial clauses in saturation        : 19
% 0.21/0.41  # Processed clauses                    : 390
% 0.21/0.41  # ...of these trivial                  : 20
% 0.21/0.41  # ...subsumed                          : 166
% 0.21/0.41  # ...remaining for further processing  : 204
% 0.21/0.41  # Other redundant clauses eliminated   : 0
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 0
% 0.21/0.41  # Backward-rewritten                   : 31
% 0.21/0.41  # Generated clauses                    : 1356
% 0.21/0.41  # ...of the previous two non-trivial   : 1212
% 0.21/0.41  # Contextual simplify-reflections      : 0
% 0.21/0.41  # Paramodulations                      : 1356
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 0
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 154
% 0.21/0.41  #    Positive orientable unit clauses  : 45
% 0.21/0.41  #    Positive unorientable unit clauses: 0
% 0.21/0.41  #    Negative unit clauses             : 1
% 0.21/0.41  #    Non-unit-clauses                  : 108
% 0.21/0.41  # Current number of unprocessed clauses: 818
% 0.21/0.41  # ...number of literals in the above   : 2156
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 50
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 2768
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1859
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 166
% 0.21/0.41  # Unit Clause-clause subsumption calls : 325
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 102
% 0.21/0.41  # BW rewrite match successes           : 2
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 21557
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.057 s
% 0.21/0.41  # System time              : 0.006 s
% 0.21/0.41  # Total time               : 0.063 s
% 0.21/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
