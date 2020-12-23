%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:45 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 239 expanded)
%              Number of clauses        :   37 (  95 expanded)
%              Number of leaves         :    8 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 (1046 expanded)
%              Number of equality atoms :   32 ( 188 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_wellord2,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_wellord2(X1,X2)
        & r2_wellord2(X2,X3) )
     => r2_wellord2(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_wellord2)).

fof(d4_wellord2,axiom,(
    ! [X1,X2] :
      ( r2_wellord2(X1,X2)
    <=> ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & v2_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord2)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc7_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2)
        & v2_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v2_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_wellord2(X1,X2)
          & r2_wellord2(X2,X3) )
       => r2_wellord2(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t22_wellord2])).

fof(c_0_9,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( v1_relat_1(esk1_2(X15,X16))
        | ~ r2_wellord2(X15,X16) )
      & ( v1_funct_1(esk1_2(X15,X16))
        | ~ r2_wellord2(X15,X16) )
      & ( v2_funct_1(esk1_2(X15,X16))
        | ~ r2_wellord2(X15,X16) )
      & ( k1_relat_1(esk1_2(X15,X16)) = X15
        | ~ r2_wellord2(X15,X16) )
      & ( k2_relat_1(esk1_2(X15,X16)) = X16
        | ~ r2_wellord2(X15,X16) )
      & ( ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v2_funct_1(X20)
        | k1_relat_1(X20) != X18
        | k2_relat_1(X20) != X19
        | r2_wellord2(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord2])])])])])])).

fof(c_0_10,negated_conjecture,
    ( r2_wellord2(esk2_0,esk3_0)
    & r2_wellord2(esk3_0,esk4_0)
    & ~ r2_wellord2(esk2_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ r1_tarski(k2_relat_1(X9),k1_relat_1(X10))
      | k1_relat_1(k5_relat_1(X9,X10)) = k1_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_12,plain,
    ( k2_relat_1(esk1_2(X1,X2)) = X2
    | ~ r2_wellord2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r2_wellord2(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk1_2(X1,X2)) = X1
    | ~ r2_wellord2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v1_relat_1(esk1_2(X1,X2))
    | ~ r2_wellord2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_17,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k2_relat_1(esk1_2(esk2_0,esk3_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk1_2(esk2_0,esk3_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( r2_wellord2(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( r2_wellord2(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_relat_1(X1) != X2
    | k2_relat_1(X1) != X3 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),X1)) = esk2_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk3_0,k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(esk1_2(esk3_0,esk4_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_wellord2(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

fof(c_0_30,plain,(
    ! [X13,X14] :
      ( ( v1_relat_1(k5_relat_1(X13,X14))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X14) )
      & ( v2_funct_1(k5_relat_1(X13,X14))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).

cnf(c_0_31,plain,
    ( v2_funct_1(esk1_2(X1,X2))
    | ~ r2_wellord2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( v1_funct_1(esk1_2(X1,X2))
    | ~ r2_wellord2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))))
    | ~ v2_funct_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))
    | ~ v1_funct_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))
    | ~ v1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v2_funct_1(esk1_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v2_funct_1(esk1_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_13])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk1_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk1_2(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_13])).

fof(c_0_39,plain,(
    ! [X11,X12] :
      ( ( v1_relat_1(k5_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v1_funct_1(k5_relat_1(X11,X12))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))))
    | ~ v1_funct_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))
    | ~ v1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_26]),c_0_20])])).

cnf(c_0_41,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_42,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | k2_relat_1(k5_relat_1(X7,X8)) = k9_relat_1(X8,k2_relat_1(X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

fof(c_0_43,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k9_relat_1(X6,k1_relat_1(X6)) = k2_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_44,negated_conjecture,
    ( r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))))
    | ~ v1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_37]),c_0_38]),c_0_26]),c_0_20])])).

cnf(c_0_45,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(esk1_2(esk3_0,esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_37]),c_0_38]),c_0_26]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( k9_relat_1(X1,esk3_0) = k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_18]),c_0_20])])).

cnf(c_0_51,negated_conjecture,
    ( k9_relat_1(esk1_2(esk3_0,esk4_0),esk3_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_26])]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_wellord2(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_26])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t22_wellord2, conjecture, ![X1, X2, X3]:((r2_wellord2(X1,X2)&r2_wellord2(X2,X3))=>r2_wellord2(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_wellord2)).
% 0.13/0.38  fof(d4_wellord2, axiom, ![X1, X2]:(r2_wellord2(X1,X2)<=>?[X3]:((((v1_relat_1(X3)&v1_funct_1(X3))&v2_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord2)).
% 0.13/0.38  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(fc7_funct_1, axiom, ![X1, X2]:((((((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))&v2_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v2_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_funct_1)).
% 0.13/0.38  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.13/0.38  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 0.13/0.38  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:((r2_wellord2(X1,X2)&r2_wellord2(X2,X3))=>r2_wellord2(X1,X3))), inference(assume_negation,[status(cth)],[t22_wellord2])).
% 0.13/0.38  fof(c_0_9, plain, ![X15, X16, X18, X19, X20]:((((((v1_relat_1(esk1_2(X15,X16))|~r2_wellord2(X15,X16))&(v1_funct_1(esk1_2(X15,X16))|~r2_wellord2(X15,X16)))&(v2_funct_1(esk1_2(X15,X16))|~r2_wellord2(X15,X16)))&(k1_relat_1(esk1_2(X15,X16))=X15|~r2_wellord2(X15,X16)))&(k2_relat_1(esk1_2(X15,X16))=X16|~r2_wellord2(X15,X16)))&(~v1_relat_1(X20)|~v1_funct_1(X20)|~v2_funct_1(X20)|k1_relat_1(X20)!=X18|k2_relat_1(X20)!=X19|r2_wellord2(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord2])])])])])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ((r2_wellord2(esk2_0,esk3_0)&r2_wellord2(esk3_0,esk4_0))&~r2_wellord2(esk2_0,esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X9, X10]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~r1_tarski(k2_relat_1(X9),k1_relat_1(X10))|k1_relat_1(k5_relat_1(X9,X10))=k1_relat_1(X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.13/0.38  cnf(c_0_12, plain, (k2_relat_1(esk1_2(X1,X2))=X2|~r2_wellord2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (r2_wellord2(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_14, plain, (k1_relat_1(esk1_2(X1,X2))=X1|~r2_wellord2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_15, plain, (v1_relat_1(esk1_2(X1,X2))|~r2_wellord2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  fof(c_0_16, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (k2_relat_1(esk1_2(esk2_0,esk3_0))=esk3_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (k1_relat_1(esk1_2(esk2_0,esk3_0))=esk2_0), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk1_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_13])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (r2_wellord2(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, plain, (r2_wellord2(X2,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|k1_relat_1(X1)!=X2|k2_relat_1(X1)!=X3), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),X1))=esk2_0|~v1_relat_1(X1)|~r1_tarski(esk3_0,k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k1_relat_1(esk1_2(esk3_0,esk4_0))=esk3_0), inference(spm,[status(thm)],[c_0_14, c_0_21])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk1_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_15, c_0_21])).
% 0.13/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_28, plain, (r2_wellord2(k1_relat_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 0.13/0.38  fof(c_0_30, plain, ![X13, X14]:((v1_relat_1(k5_relat_1(X13,X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)|~v2_funct_1(X13)|~v1_relat_1(X14)|~v1_funct_1(X14)|~v2_funct_1(X14)))&(v2_funct_1(k5_relat_1(X13,X14))|(~v1_relat_1(X13)|~v1_funct_1(X13)|~v2_funct_1(X13)|~v1_relat_1(X14)|~v1_funct_1(X14)|~v2_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_funct_1])])])).
% 0.13/0.38  cnf(c_0_31, plain, (v2_funct_1(esk1_2(X1,X2))|~r2_wellord2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_32, plain, (v1_funct_1(esk1_2(X1,X2))|~r2_wellord2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))))|~v2_funct_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))|~v1_funct_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))|~v1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v2_funct_1(esk1_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_21])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (v2_funct_1(esk1_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_31, c_0_13])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk1_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk1_2(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_13])).
% 0.13/0.38  fof(c_0_39, plain, ![X11, X12]:((v1_relat_1(k5_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)|~v1_relat_1(X12)|~v1_funct_1(X12)))&(v1_funct_1(k5_relat_1(X11,X12))|(~v1_relat_1(X11)|~v1_funct_1(X11)|~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))))|~v1_funct_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))|~v1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_26]), c_0_20])])).
% 0.13/0.38  cnf(c_0_41, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  fof(c_0_42, plain, ![X7, X8]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|k2_relat_1(k5_relat_1(X7,X8))=k9_relat_1(X8,k2_relat_1(X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.13/0.38  fof(c_0_43, plain, ![X6]:(~v1_relat_1(X6)|k9_relat_1(X6,k1_relat_1(X6))=k2_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))))|~v1_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_37]), c_0_38]), c_0_26]), c_0_20])])).
% 0.13/0.38  cnf(c_0_45, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_46, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_47, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k2_relat_1(esk1_2(esk3_0,esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_12, c_0_21])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (r2_wellord2(esk2_0,k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),esk1_2(esk3_0,esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_37]), c_0_38]), c_0_26]), c_0_20])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k9_relat_1(X1,esk3_0)=k2_relat_1(k5_relat_1(esk1_2(esk2_0,esk3_0),X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_18]), c_0_20])])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (k9_relat_1(esk1_2(esk3_0,esk4_0),esk3_0)=esk4_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_26])]), c_0_48])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (~r2_wellord2(esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_26])]), c_0_52]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 54
% 0.13/0.38  # Proof object clause steps            : 37
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 19
% 0.13/0.38  # Proof object simplifying inferences  : 35
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 82
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 6
% 0.13/0.38  # ...remaining for further processing  : 74
% 0.13/0.38  # Other redundant clauses eliminated   : 4
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 140
% 0.13/0.38  # ...of the previous two non-trivial   : 109
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 137
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 4
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 50
% 0.13/0.38  #    Positive orientable unit clauses  : 18
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 58
% 0.13/0.38  # ...number of literals in the above   : 326
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 21
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 103
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 62
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.13/0.38  # Unit Clause-clause subsumption calls : 13
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5201
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.036 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
