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
% DateTime   : Thu Dec  3 10:53:43 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 205 expanded)
%              Number of clauses        :   32 (  77 expanded)
%              Number of leaves         :    7 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  191 (1046 expanded)
%              Number of equality atoms :   33 ( 184 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   48 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t49_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
                    & r1_tarski(k2_relat_1(X3),k1_relat_1(X1))
                    & k1_relat_1(X2) = k1_relat_1(X3)
                    & k5_relat_1(X2,X1) = k5_relat_1(X3,X1) )
                 => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(t27_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
           => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(t47_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( ? [X2] :
              ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
         => v2_funct_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t53_funct_1])).

fof(c_0_8,plain,(
    ! [X4] :
      ( k1_relat_1(k6_relat_1(X4)) = X4
      & k2_relat_1(k6_relat_1(X4)) = X4 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0))
    & ~ v2_funct_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X7] :
      ( v1_relat_1(k6_relat_1(X7))
      & v1_funct_1(k6_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_11,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ r1_tarski(k2_relat_1(X13),k1_relat_1(X12))
        | ~ r1_tarski(k2_relat_1(X14),k1_relat_1(X12))
        | k1_relat_1(X13) != k1_relat_1(X14)
        | k5_relat_1(X13,X12) != k5_relat_1(X14,X12)
        | X13 = X14
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v1_relat_1(esk1_1(X12))
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v1_funct_1(esk1_1(X12))
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v1_relat_1(esk2_1(X12))
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v1_funct_1(esk2_1(X12))
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r1_tarski(k2_relat_1(esk1_1(X12)),k1_relat_1(X12))
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r1_tarski(k2_relat_1(esk2_1(X12)),k1_relat_1(X12))
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_relat_1(esk1_1(X12)) = k1_relat_1(esk2_1(X12))
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k5_relat_1(esk1_1(X12),X12) = k5_relat_1(esk2_1(X12),X12)
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk1_1(X12) != esk2_1(X12)
        | v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_funct_1])])])])])).

cnf(c_0_12,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(X6),X5)
      | k5_relat_1(X6,k6_relat_1(X5)) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_relat_1(esk2_1(X1)),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_relat_1(esk1_1(X1)),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0))
    | r1_tarski(k2_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0))
    | r1_tarski(k2_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0))),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0)) = esk2_1(k5_relat_1(esk3_0,esk4_0))
    | v2_funct_1(k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_13])).

cnf(c_0_26,plain,
    ( v1_relat_1(esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( k5_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0)) = esk1_1(k5_relat_1(esk3_0,esk4_0))
    | v2_funct_1(k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_24]),c_0_13])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk1_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,plain,
    ( k5_relat_1(esk1_1(X1),X1) = k5_relat_1(esk2_1(X1),X1)
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k5_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0)) = esk2_1(k5_relat_1(esk3_0,esk4_0))
    | v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_19]),c_0_20])])).

cnf(c_0_31,negated_conjecture,
    ( k5_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0)) = esk1_1(k5_relat_1(esk3_0,esk4_0))
    | v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19]),c_0_20])])).

cnf(c_0_32,negated_conjecture,
    ( k5_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0)) = esk2_1(k5_relat_1(esk3_0,esk4_0))
    | v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19]),c_0_20])])).

fof(c_0_33,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_funct_1(X9)
      | k1_relat_1(k5_relat_1(X9,X8)) != k1_relat_1(X9)
      | r1_tarski(k2_relat_1(X9),k1_relat_1(X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).

fof(c_0_34,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ v2_funct_1(k5_relat_1(X11,X10))
      | ~ r1_tarski(k2_relat_1(X11),k1_relat_1(X10))
      | v2_funct_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).

cnf(c_0_35,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( esk2_1(k5_relat_1(esk3_0,esk4_0)) = esk1_1(k5_relat_1(esk3_0,esk4_0))
    | v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(k5_relat_1(X2,X1)) != k1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,plain,
    ( v2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_19]),c_0_20])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_38]),c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_38]),c_0_39]),c_0_44]),c_0_40]),c_0_41])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:50:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S04DN
% 0.13/0.38  # and selection function SelectNewComplex.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t53_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 0.13/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.38  fof(t49_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((((r1_tarski(k2_relat_1(X2),k1_relat_1(X1))&r1_tarski(k2_relat_1(X3),k1_relat_1(X1)))&k1_relat_1(X2)=k1_relat_1(X3))&k5_relat_1(X2,X1)=k5_relat_1(X3,X1))=>X2=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_1)).
% 0.13/0.38  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.13/0.38  fof(t27_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(k5_relat_1(X2,X1))=k1_relat_1(X2)=>r1_tarski(k2_relat_1(X2),k1_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 0.13/0.38  fof(t47_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&r1_tarski(k2_relat_1(X2),k1_relat_1(X1)))=>v2_funct_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1)))), inference(assume_negation,[status(cth)],[t53_funct_1])).
% 0.13/0.38  fof(c_0_8, plain, ![X4]:(k1_relat_1(k6_relat_1(X4))=X4&k2_relat_1(k6_relat_1(X4))=X4), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0)))&~v2_funct_1(esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X7]:(v1_relat_1(k6_relat_1(X7))&v1_funct_1(k6_relat_1(X7))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X12, X13, X14]:((~v2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14)|(~r1_tarski(k2_relat_1(X13),k1_relat_1(X12))|~r1_tarski(k2_relat_1(X14),k1_relat_1(X12))|k1_relat_1(X13)!=k1_relat_1(X14)|k5_relat_1(X13,X12)!=k5_relat_1(X14,X12)|X13=X14)))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(((v1_relat_1(esk1_1(X12))|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(v1_funct_1(esk1_1(X12))|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(((v1_relat_1(esk2_1(X12))|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(v1_funct_1(esk2_1(X12))|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(((((r1_tarski(k2_relat_1(esk1_1(X12)),k1_relat_1(X12))|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(r1_tarski(k2_relat_1(esk2_1(X12)),k1_relat_1(X12))|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(k1_relat_1(esk1_1(X12))=k1_relat_1(esk2_1(X12))|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(k5_relat_1(esk1_1(X12),X12)=k5_relat_1(esk2_1(X12),X12)|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(esk1_1(X12)!=esk2_1(X12)|v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_funct_1])])])])])).
% 0.13/0.38  cnf(c_0_12, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_13, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_14, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_15, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_16, plain, ![X5, X6]:(~v1_relat_1(X6)|(~r1_tarski(k2_relat_1(X6),X5)|k5_relat_1(X6,k6_relat_1(X5))=X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.13/0.38  cnf(c_0_17, plain, (r1_tarski(k2_relat_1(esk2_1(X1)),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_14, c_0_13])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_15, c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (r1_tarski(k2_relat_1(esk1_1(X1)),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_22, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))|r1_tarski(k2_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))|r1_tarski(k2_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0))),k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (k5_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0))=esk2_1(k5_relat_1(esk3_0,esk4_0))|v2_funct_1(k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_13])).
% 0.13/0.38  cnf(c_0_26, plain, (v1_relat_1(esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (k5_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0))=esk1_1(k5_relat_1(esk3_0,esk4_0))|v2_funct_1(k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_24]), c_0_13])).
% 0.13/0.38  cnf(c_0_28, plain, (v1_relat_1(esk1_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_29, plain, (k5_relat_1(esk1_1(X1),X1)=k5_relat_1(esk2_1(X1),X1)|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k5_relat_1(esk2_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0))=esk2_1(k5_relat_1(esk3_0,esk4_0))|v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (k5_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0))=esk1_1(k5_relat_1(esk3_0,esk4_0))|v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (k5_relat_1(esk1_1(k5_relat_1(esk3_0,esk4_0)),k5_relat_1(esk3_0,esk4_0))=esk2_1(k5_relat_1(esk3_0,esk4_0))|v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19]), c_0_20])])).
% 0.13/0.38  fof(c_0_33, plain, ![X8, X9]:(~v1_relat_1(X8)|~v1_funct_1(X8)|(~v1_relat_1(X9)|~v1_funct_1(X9)|(k1_relat_1(k5_relat_1(X9,X8))!=k1_relat_1(X9)|r1_tarski(k2_relat_1(X9),k1_relat_1(X8))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t27_funct_1])])])).
% 0.13/0.38  fof(c_0_34, plain, ![X10, X11]:(~v1_relat_1(X10)|~v1_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11)|(~v2_funct_1(k5_relat_1(X11,X10))|~r1_tarski(k2_relat_1(X11),k1_relat_1(X10))|v2_funct_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).
% 0.13/0.38  cnf(c_0_35, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (esk2_1(k5_relat_1(esk3_0,esk4_0))=esk1_1(k5_relat_1(esk3_0,esk4_0))|v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.38  cnf(c_0_37, plain, (r1_tarski(k2_relat_1(X2),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(k5_relat_1(X2,X1))!=k1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_42, plain, (v2_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(k5_relat_1(X2,X1))|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_19]), c_0_20])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_18]), c_0_38]), c_0_39]), c_0_40]), c_0_41])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_38]), c_0_39]), c_0_44]), c_0_40]), c_0_41])]), c_0_45]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 47
% 0.13/0.38  # Proof object clause steps            : 32
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 23
% 0.13/0.38  # Proof object clause conjectures      : 20
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 18
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 14
% 0.13/0.38  # Proof object simplifying inferences  : 32
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 23
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 23
% 0.13/0.38  # Processed clauses                    : 73
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 1
% 0.13/0.38  # ...remaining for further processing  : 72
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 2
% 0.13/0.38  # Backward-rewritten                   : 7
% 0.13/0.38  # Generated clauses                    : 80
% 0.13/0.38  # ...of the previous two non-trivial   : 63
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 77
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 40
% 0.13/0.38  #    Positive orientable unit clauses  : 20
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 36
% 0.13/0.38  # ...number of literals in the above   : 183
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 32
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 59
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 7
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 3
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4197
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
