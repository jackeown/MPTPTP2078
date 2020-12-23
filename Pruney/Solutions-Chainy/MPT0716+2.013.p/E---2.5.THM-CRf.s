%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 596 expanded)
%              Number of clauses        :   38 ( 264 expanded)
%              Number of leaves         :    7 ( 144 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 (2708 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(c_0_7,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,negated_conjecture,(
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

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | r1_tarski(k1_relat_1(k5_relat_1(X15,X16)),k1_relat_1(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
    | ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(X2,k1_relat_1(esk2_0))
    | ~ r1_tarski(esk4_0,X2)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk2_0,X1)),k1_relat_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X2)
    | ~ r1_tarski(X3,k1_relat_1(esk2_0))
    | ~ r1_tarski(X2,k1_relat_1(esk3_0))
    | ~ r1_tarski(esk4_0,X3)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_11])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k1_relat_1(k5_relat_1(X13,X14)) = k10_relat_1(X13,k1_relat_1(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk2_0,esk3_0)),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X2)
    | ~ r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r1_tarski(X2,k1_relat_1(esk3_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | r1_tarski(k9_relat_1(X18,k10_relat_1(X18,X17)),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_31,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X2)
    | ~ r1_tarski(X2,k1_relat_1(esk3_0))
    | ~ r1_tarski(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(esk2_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

fof(c_0_36,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r1_tarski(X10,X11)
      | r1_tarski(k9_relat_1(X12,X10),k9_relat_1(X12,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_25])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_relat_1(esk3_0)) = k1_relat_1(k5_relat_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_40,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ r1_tarski(X19,k1_relat_1(X21))
      | ~ r1_tarski(k9_relat_1(X21,X19),X20)
      | r1_tarski(X19,k10_relat_1(X21,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k9_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_44,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,k10_relat_1(esk2_0,X1))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34]),c_0_20])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))
    | r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))
    | ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_39]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk2_0,esk4_0),k9_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_43]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.20/0.38  # and selection function PSelectMinOptimalNoXTypePred.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 0.20/0.38  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.20/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.38  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.20/0.38  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.20/0.38  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.20/0.38  fof(c_0_7, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.20/0.38  cnf(c_0_9, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_10, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|(~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))))&((r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))&(r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.20/0.38  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.38  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_16, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.38  fof(c_0_17, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|r1_tarski(k1_relat_1(k5_relat_1(X15,X16)),k1_relat_1(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|~r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.38  cnf(c_0_19, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|~r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(X2,k1_relat_1(esk2_0))|~r1_tarski(esk4_0,X2)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk2_0,X1)),k1_relat_1(esk2_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (~r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X2)|~r1_tarski(X3,k1_relat_1(esk2_0))|~r1_tarski(X2,k1_relat_1(esk3_0))|~r1_tarski(esk4_0,X3)|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.20/0.38  cnf(c_0_25, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_9, c_0_11])).
% 0.20/0.38  fof(c_0_26, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|k1_relat_1(k5_relat_1(X13,X14))=k10_relat_1(X13,k1_relat_1(X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk2_0,esk3_0)),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (~r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X2)|~r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(X2,k1_relat_1(esk3_0))|~r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  fof(c_0_30, plain, ![X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|r1_tarski(k9_relat_1(X18,k10_relat_1(X18,X17)),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.20/0.38  cnf(c_0_31, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (~r1_tarski(X1,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X2)|~r1_tarski(X2,k1_relat_1(esk3_0))|~r1_tarski(esk4_0,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_27]), c_0_28])]), c_0_29])).
% 0.20/0.38  cnf(c_0_33, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (k10_relat_1(esk2_0,k1_relat_1(X1))=k1_relat_1(k5_relat_1(esk2_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.20/0.38  fof(c_0_36, plain, ![X10, X11, X12]:(~v1_relat_1(X12)|(~r1_tarski(X10,X11)|r1_tarski(k9_relat_1(X12,X10),k9_relat_1(X12,X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_25])])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,k10_relat_1(esk2_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_20])])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (k10_relat_1(esk2_0,k1_relat_1(esk3_0))=k1_relat_1(k5_relat_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_35, c_0_23])).
% 0.20/0.38  cnf(c_0_40, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  fof(c_0_41, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~r1_tarski(X19,k1_relat_1(X21))|~r1_tarski(k9_relat_1(X21,X19),X20)|r1_tarski(X19,k10_relat_1(X21,X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),k9_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,X1),k9_relat_1(esk2_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 0.20/0.38  cnf(c_0_44, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_27])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(esk4_0,k10_relat_1(esk2_0,X1))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_34]), c_0_20])])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,esk4_0),k1_relat_1(esk3_0))|r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (~r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))|~r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_25])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (r1_tarski(esk4_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_39]), c_0_47])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk4_0),X1)|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (~r1_tarski(k9_relat_1(esk2_0,esk4_0),k9_relat_1(esk2_0,k1_relat_1(k5_relat_1(esk2_0,esk3_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_43]), c_0_49])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 53
% 0.20/0.38  # Proof object clause steps            : 38
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 29
% 0.20/0.38  # Proof object clause conjectures      : 26
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 14
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 23
% 0.20/0.38  # Proof object simplifying inferences  : 18
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 15
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 15
% 0.20/0.38  # Processed clauses                    : 123
% 0.20/0.38  # ...of these trivial                  : 4
% 0.20/0.38  # ...subsumed                          : 14
% 0.20/0.38  # ...remaining for further processing  : 105
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 17
% 0.20/0.38  # Backward-rewritten                   : 4
% 0.20/0.38  # Generated clauses                    : 261
% 0.20/0.38  # ...of the previous two non-trivial   : 249
% 0.20/0.38  # Contextual simplify-reflections      : 3
% 0.20/0.38  # Paramodulations                      : 261
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
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
% 0.20/0.38  # Current number of processed clauses  : 69
% 0.20/0.38  #    Positive orientable unit clauses  : 28
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 5
% 0.20/0.38  #    Non-unit-clauses                  : 36
% 0.20/0.38  # Current number of unprocessed clauses: 144
% 0.20/0.38  # ...number of literals in the above   : 435
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 36
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 467
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 230
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 26
% 0.20/0.38  # Unit Clause-clause subsumption calls : 37
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 18
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 6187
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.038 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.040 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
