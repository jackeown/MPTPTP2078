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
% DateTime   : Thu Dec  3 10:55:06 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 133 expanded)
%              Number of clauses        :   33 (  50 expanded)
%              Number of leaves         :   13 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  182 ( 383 expanded)
%              Number of equality atoms :   34 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t154_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t46_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X2) )
           => v2_funct_1(k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t66_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X2) )
           => k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(t67_funct_1,axiom,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t154_funct_1])).

fof(c_0_14,plain,(
    ! [X21] :
      ( ( v1_relat_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_funct_1(esk3_0)
    & k9_relat_1(esk3_0,esk2_0) != k10_relat_1(k2_funct_1(esk3_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ v2_funct_1(X29)
      | ~ v2_funct_1(X30)
      | v2_funct_1(k5_relat_1(X29,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_funct_1])])])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( ( v1_relat_1(k5_relat_1(X22,X23))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( v1_funct_1(k5_relat_1(X22,X23))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_18,plain,(
    ! [X24] :
      ( v1_relat_1(k6_relat_1(X24))
      & v1_funct_1(k6_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_19,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | v1_relat_1(k5_relat_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_20,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v2_funct_1(X32)
      | ~ v2_funct_1(X33)
      | k2_funct_1(k5_relat_1(X32,X33)) = k5_relat_1(k2_funct_1(X33),k2_funct_1(X32)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).

fof(c_0_21,plain,(
    ! [X34] : k2_funct_1(k6_relat_1(X34)) = k6_relat_1(X34) ),
    inference(variable_rename,[status(thm)],[t67_funct_1])).

fof(c_0_22,plain,(
    ! [X25] :
      ( v1_relat_1(k6_relat_1(X25))
      & v2_funct_1(k6_relat_1(X25)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_23,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | k1_relat_1(k5_relat_1(X13,X14)) = k10_relat_1(X13,k1_relat_1(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | k2_relat_1(k5_relat_1(X11,X12)) = k9_relat_1(X12,k2_relat_1(X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

cnf(c_0_28,plain,
    ( v2_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_39,plain,(
    ! [X18] :
      ( k1_relat_1(k6_relat_1(X18)) = X18
      & k2_relat_1(k6_relat_1(X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_40,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_41,plain,(
    ! [X31] :
      ( ( k2_relat_1(X31) = k1_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( k1_relat_1(X31) = k2_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_42,negated_conjecture,
    ( v2_funct_1(k5_relat_1(X1,esk3_0))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_29]),c_0_25])])).

cnf(c_0_43,plain,
    ( v1_funct_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_45,plain,
    ( k2_funct_1(k5_relat_1(k6_relat_1(X1),X2)) = k5_relat_1(k2_funct_1(X2),k6_relat_1(X1))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_35]),c_0_36]),c_0_32])])).

cnf(c_0_46,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk3_0),k1_relat_1(X1)) = k1_relat_1(k5_relat_1(k2_funct_1(esk3_0),X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k9_relat_1(esk3_0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_26])).

cnf(c_0_49,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(k5_relat_1(k6_relat_1(X1),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_36]),c_0_31])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(k5_relat_1(k6_relat_1(X1),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_26])])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_54,negated_conjecture,
    ( k2_funct_1(k5_relat_1(k6_relat_1(X1),esk3_0)) = k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_25]),c_0_29]),c_0_26])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))) = k10_relat_1(k2_funct_1(esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k6_relat_1(X1),esk3_0)) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_31]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) != k10_relat_1(k2_funct_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk3_0),X1) = k9_relat_1(esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])]),c_0_54]),c_0_55]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.83/4.05  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05DN
% 3.83/4.05  # and selection function SelectDivLits.
% 3.83/4.05  #
% 3.83/4.05  # Preprocessing time       : 0.028 s
% 3.83/4.05  # Presaturation interreduction done
% 3.83/4.05  
% 3.83/4.05  # Proof found!
% 3.83/4.05  # SZS status Theorem
% 3.83/4.05  # SZS output start CNFRefutation
% 3.83/4.05  fof(t154_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k9_relat_1(X2,X1)=k10_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 3.83/4.05  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.83/4.05  fof(t46_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>v2_funct_1(k5_relat_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_funct_1)).
% 3.83/4.05  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 3.83/4.05  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.83/4.05  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.83/4.05  fof(t66_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 3.83/4.05  fof(t67_funct_1, axiom, ![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 3.83/4.05  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.83/4.05  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 3.83/4.05  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 3.83/4.05  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.83/4.05  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.83/4.05  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k9_relat_1(X2,X1)=k10_relat_1(k2_funct_1(X2),X1)))), inference(assume_negation,[status(cth)],[t154_funct_1])).
% 3.83/4.05  fof(c_0_14, plain, ![X21]:((v1_relat_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(v1_funct_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 3.83/4.05  fof(c_0_15, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(v2_funct_1(esk3_0)&k9_relat_1(esk3_0,esk2_0)!=k10_relat_1(k2_funct_1(esk3_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 3.83/4.05  fof(c_0_16, plain, ![X29, X30]:(~v1_relat_1(X29)|~v1_funct_1(X29)|(~v1_relat_1(X30)|~v1_funct_1(X30)|(~v2_funct_1(X29)|~v2_funct_1(X30)|v2_funct_1(k5_relat_1(X29,X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_funct_1])])])).
% 3.83/4.05  fof(c_0_17, plain, ![X22, X23]:((v1_relat_1(k5_relat_1(X22,X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)|~v1_relat_1(X23)|~v1_funct_1(X23)))&(v1_funct_1(k5_relat_1(X22,X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)|~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 3.83/4.05  fof(c_0_18, plain, ![X24]:(v1_relat_1(k6_relat_1(X24))&v1_funct_1(k6_relat_1(X24))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 3.83/4.05  fof(c_0_19, plain, ![X7, X8]:(~v1_relat_1(X7)|~v1_relat_1(X8)|v1_relat_1(k5_relat_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 3.83/4.05  fof(c_0_20, plain, ![X32, X33]:(~v1_relat_1(X32)|~v1_funct_1(X32)|(~v1_relat_1(X33)|~v1_funct_1(X33)|(~v2_funct_1(X32)|~v2_funct_1(X33)|k2_funct_1(k5_relat_1(X32,X33))=k5_relat_1(k2_funct_1(X33),k2_funct_1(X32))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).
% 3.83/4.05  fof(c_0_21, plain, ![X34]:k2_funct_1(k6_relat_1(X34))=k6_relat_1(X34), inference(variable_rename,[status(thm)],[t67_funct_1])).
% 3.83/4.05  fof(c_0_22, plain, ![X25]:(v1_relat_1(k6_relat_1(X25))&v2_funct_1(k6_relat_1(X25))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 3.83/4.05  fof(c_0_23, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|k1_relat_1(k5_relat_1(X13,X14))=k10_relat_1(X13,k1_relat_1(X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 3.83/4.05  cnf(c_0_24, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.83/4.05  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.83/4.05  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.83/4.05  fof(c_0_27, plain, ![X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|k2_relat_1(k5_relat_1(X11,X12))=k9_relat_1(X12,k2_relat_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 3.83/4.05  cnf(c_0_28, plain, (v2_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.83/4.05  cnf(c_0_29, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.83/4.05  cnf(c_0_30, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.83/4.05  cnf(c_0_31, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.83/4.05  cnf(c_0_32, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.83/4.05  cnf(c_0_33, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.83/4.05  cnf(c_0_34, plain, (k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.83/4.05  cnf(c_0_35, plain, (k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.83/4.05  cnf(c_0_36, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.83/4.05  cnf(c_0_37, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.83/4.05  cnf(c_0_38, negated_conjecture, (v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 3.83/4.05  fof(c_0_39, plain, ![X18]:(k1_relat_1(k6_relat_1(X18))=X18&k2_relat_1(k6_relat_1(X18))=X18), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 3.83/4.05  cnf(c_0_40, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.83/4.05  fof(c_0_41, plain, ![X31]:((k2_relat_1(X31)=k1_relat_1(k2_funct_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(k1_relat_1(X31)=k2_relat_1(k2_funct_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 3.83/4.05  cnf(c_0_42, negated_conjecture, (v2_funct_1(k5_relat_1(X1,esk3_0))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_29]), c_0_25])])).
% 3.83/4.05  cnf(c_0_43, plain, (v1_funct_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 3.83/4.05  cnf(c_0_44, negated_conjecture, (v1_relat_1(k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 3.83/4.05  cnf(c_0_45, plain, (k2_funct_1(k5_relat_1(k6_relat_1(X1),X2))=k5_relat_1(k2_funct_1(X2),k6_relat_1(X1))|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_31]), c_0_35]), c_0_36]), c_0_32])])).
% 3.83/4.05  cnf(c_0_46, negated_conjecture, (k10_relat_1(k2_funct_1(esk3_0),k1_relat_1(X1))=k1_relat_1(k5_relat_1(k2_funct_1(esk3_0),X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.83/4.05  cnf(c_0_47, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.83/4.05  cnf(c_0_48, negated_conjecture, (k9_relat_1(esk3_0,k2_relat_1(X1))=k2_relat_1(k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_26])).
% 3.83/4.05  cnf(c_0_49, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 3.83/4.05  cnf(c_0_50, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 3.83/4.05  cnf(c_0_51, negated_conjecture, (v2_funct_1(k5_relat_1(k6_relat_1(X1),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_36]), c_0_31])])).
% 3.83/4.05  cnf(c_0_52, negated_conjecture, (v1_funct_1(k5_relat_1(k6_relat_1(X1),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_26])])).
% 3.83/4.05  cnf(c_0_53, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(X1),esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 3.83/4.05  cnf(c_0_54, negated_conjecture, (k2_funct_1(k5_relat_1(k6_relat_1(X1),esk3_0))=k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_25]), c_0_29]), c_0_26])])).
% 3.83/4.05  cnf(c_0_55, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(X1)))=k10_relat_1(k2_funct_1(esk3_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_47])).
% 3.83/4.05  cnf(c_0_56, negated_conjecture, (k2_relat_1(k5_relat_1(k6_relat_1(X1),esk3_0))=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_31]), c_0_49])).
% 3.83/4.05  cnf(c_0_57, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)!=k10_relat_1(k2_funct_1(esk3_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 3.83/4.05  cnf(c_0_58, negated_conjecture, (k10_relat_1(k2_funct_1(esk3_0),X1)=k9_relat_1(esk3_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])]), c_0_54]), c_0_55]), c_0_56])).
% 3.83/4.05  cnf(c_0_59, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])]), ['proof']).
% 3.83/4.05  # SZS output end CNFRefutation
% 3.83/4.05  # Proof object total steps             : 60
% 3.83/4.05  # Proof object clause steps            : 33
% 3.83/4.05  # Proof object formula steps           : 27
% 3.83/4.05  # Proof object conjectures             : 20
% 3.83/4.05  # Proof object clause conjectures      : 17
% 3.83/4.05  # Proof object formula conjectures     : 3
% 3.83/4.05  # Proof object initial clauses used    : 18
% 3.83/4.05  # Proof object initial formulas used   : 13
% 3.83/4.05  # Proof object generating inferences   : 14
% 3.83/4.05  # Proof object simplifying inferences  : 29
% 3.83/4.05  # Training examples: 0 positive, 0 negative
% 3.83/4.05  # Parsed axioms                        : 19
% 3.83/4.05  # Removed by relevancy pruning/SinE    : 0
% 3.83/4.05  # Initial clauses                      : 31
% 3.83/4.05  # Removed in clause preprocessing      : 0
% 3.83/4.05  # Initial clauses in saturation        : 31
% 3.83/4.05  # Processed clauses                    : 2844
% 3.83/4.05  # ...of these trivial                  : 2
% 3.83/4.05  # ...subsumed                          : 18
% 3.83/4.05  # ...remaining for further processing  : 2824
% 3.83/4.05  # Other redundant clauses eliminated   : 6
% 3.83/4.05  # Clauses deleted for lack of memory   : 0
% 3.83/4.05  # Backward-subsumed                    : 0
% 3.83/4.05  # Backward-rewritten                   : 37
% 3.83/4.05  # Generated clauses                    : 649678
% 3.83/4.05  # ...of the previous two non-trivial   : 649673
% 3.83/4.05  # Contextual simplify-reflections      : 0
% 3.83/4.05  # Paramodulations                      : 649671
% 3.83/4.05  # Factorizations                       : 0
% 3.83/4.05  # Equation resolutions                 : 7
% 3.83/4.05  # Propositional unsat checks           : 0
% 3.83/4.05  #    Propositional check models        : 0
% 3.83/4.05  #    Propositional check unsatisfiable : 0
% 3.83/4.05  #    Propositional clauses             : 0
% 3.83/4.05  #    Propositional clauses after purity: 0
% 3.83/4.05  #    Propositional unsat core size     : 0
% 3.83/4.05  #    Propositional preprocessing time  : 0.000
% 3.83/4.05  #    Propositional encoding time       : 0.000
% 3.83/4.05  #    Propositional solver time         : 0.000
% 3.83/4.05  #    Success case prop preproc time    : 0.000
% 3.83/4.05  #    Success case prop encoding time   : 0.000
% 3.83/4.05  #    Success case prop solver time     : 0.000
% 3.83/4.05  # Current number of processed clauses  : 2758
% 3.83/4.05  #    Positive orientable unit clauses  : 1827
% 3.83/4.05  #    Positive unorientable unit clauses: 0
% 3.83/4.05  #    Negative unit clauses             : 0
% 3.83/4.05  #    Non-unit-clauses                  : 931
% 3.83/4.05  # Current number of unprocessed clauses: 646832
% 3.83/4.05  # ...number of literals in the above   : 758140
% 3.83/4.05  # Current number of archived formulas  : 0
% 3.83/4.05  # Current number of archived clauses   : 66
% 3.83/4.05  # Clause-clause subsumption calls (NU) : 44808
% 3.83/4.05  # Rec. Clause-clause subsumption calls : 35987
% 3.83/4.05  # Non-unit clause-clause subsumptions  : 18
% 3.83/4.05  # Unit Clause-clause subsumption calls : 2825
% 3.83/4.05  # Rewrite failures with RHS unbound    : 0
% 3.83/4.05  # BW rewrite match attempts            : 91677
% 3.83/4.05  # BW rewrite match successes           : 16
% 3.83/4.05  # Condensation attempts                : 0
% 3.83/4.05  # Condensation successes               : 0
% 3.83/4.05  # Termbank termtop insertions          : 15985336
% 3.91/4.07  
% 3.91/4.07  # -------------------------------------------------
% 3.91/4.07  # User time                : 3.415 s
% 3.91/4.07  # System time              : 0.315 s
% 3.91/4.07  # Total time               : 3.730 s
% 3.91/4.07  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
