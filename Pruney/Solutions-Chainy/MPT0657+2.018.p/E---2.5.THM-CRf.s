%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:07 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   77 (1453 expanded)
%              Number of clauses        :   52 ( 503 expanded)
%              Number of leaves         :   12 ( 367 expanded)
%              Depth                    :   17
%              Number of atoms          :  228 (6926 expanded)
%              Number of equality atoms :   75 (2517 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X2) = k1_relat_1(X1)
              & k5_relat_1(X2,X1) = k6_relat_1(k2_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t44_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = X1 )
           => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & k2_relat_1(X2) = k1_relat_1(X1)
                & k5_relat_1(X2,X1) = k6_relat_1(k2_relat_1(X1)) )
             => X2 = k2_funct_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_1])).

fof(c_0_13,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k10_relat_1(X6,k2_relat_1(X6)) = k1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk1_0)
    & k2_relat_1(esk2_0) = k1_relat_1(esk1_0)
    & k5_relat_1(esk2_0,esk1_0) = k6_relat_1(k2_relat_1(esk1_0))
    & esk2_0 != k2_funct_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | k1_relat_1(k5_relat_1(X7,X8)) = k10_relat_1(X7,k1_relat_1(X8)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X12] :
      ( k1_relat_1(k6_relat_1(X12)) = X12
      & k2_relat_1(k6_relat_1(X12)) = X12 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | v1_relat_1(k5_relat_1(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_21,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(X9,X10),X11) = k5_relat_1(X9,k5_relat_1(X10,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_22,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | k5_relat_1(k6_relat_1(k1_relat_1(X13)),X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_23,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_relat_1(esk1_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(esk2_0,esk1_0) = k6_relat_1(k2_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(esk2_0) = k2_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_18])])).

fof(c_0_32,plain,(
    ! [X20] :
      ( ( k5_relat_1(X20,k2_funct_1(X20)) = k6_relat_1(k1_relat_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( k5_relat_1(k2_funct_1(X20),X20) = k6_relat_1(k2_relat_1(X20))
        | ~ v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_33,plain,
    ( v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_18])])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k6_relat_1(k2_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_27]),c_0_18])])).

cnf(c_0_36,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( k10_relat_1(X1,k2_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_31]),c_0_18])])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_18]),c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( k5_relat_1(esk1_0,k2_funct_1(esk1_0)) = k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_27])])).

fof(c_0_42,plain,(
    ! [X14] :
      ( ( v1_relat_1(k2_funct_1(X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( v1_funct_1(k2_funct_1(X14))
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_43,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(X1,k10_relat_1(X2,k2_relat_1(esk1_0))) = k1_relat_1(k5_relat_1(X1,k5_relat_1(X2,esk2_0)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_39]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(k6_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_41]),c_0_27])])).

cnf(c_0_46,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk2_0)) = k1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(esk1_0))))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_39]),c_0_35])])).

fof(c_0_48,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | k2_relat_1(X17) != k1_relat_1(X18)
      | k5_relat_1(X17,X18) != X17
      | X18 = k6_relat_1(k1_relat_1(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).

cnf(c_0_49,negated_conjecture,
    ( k10_relat_1(X1,k1_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,k5_relat_1(esk1_0,esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_27])])).

cnf(c_0_50,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),k5_relat_1(X1,X2)) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(X1)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(k6_relat_1(k1_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_38]),c_0_27])])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(X1,k2_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(esk1_0))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k10_relat_1(X1,k2_relat_1(esk1_0))),k5_relat_1(X1,esk2_0)) = k5_relat_1(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_40])).

cnf(c_0_54,plain,
    ( X2 = k6_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k5_relat_1(esk2_0,k5_relat_1(esk1_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_27]),c_0_18])])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,esk2_0)) = k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_18]),c_0_27])])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,k6_relat_1(k2_relat_1(esk1_0)))) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_52]),c_0_27])])).

cnf(c_0_59,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,esk2_0)) = k5_relat_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_16]),c_0_27])])).

cnf(c_0_60,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k5_relat_1(esk1_0,X1))) = k5_relat_1(esk1_0,X1)
    | k1_relat_1(k5_relat_1(esk1_0,X1)) != k1_relat_1(esk1_0)
    | k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1) != esk2_0
    | ~ v1_funct_1(k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_17]),c_0_56]),c_0_18])])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_57]),c_0_58]),c_0_27])])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_59]),c_0_18]),c_0_27]),c_0_51])])).

fof(c_0_63,plain,(
    ! [X15,X16] :
      ( ( v1_relat_1(k5_relat_1(X15,X16))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( v1_funct_1(k5_relat_1(X15,X16))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_64,negated_conjecture,
    ( k5_relat_1(esk1_0,esk2_0) = k6_relat_1(k1_relat_1(esk1_0))
    | ~ v1_funct_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_34]),c_0_57]),c_0_61]),c_0_57]),c_0_61]),c_0_62]),c_0_18])])).

cnf(c_0_65,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_66,plain,(
    ! [X19] :
      ( ( k2_relat_1(X19) = k1_relat_1(k2_funct_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k1_relat_1(X19) = k2_relat_1(k2_funct_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_67,negated_conjecture,
    ( k5_relat_1(esk1_0,esk2_0) = k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_56]),c_0_38]),c_0_18]),c_0_27])])).

cnf(c_0_68,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk1_0))) = k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_41])).

cnf(c_0_70,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk1_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_67]),c_0_34]),c_0_18])])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk1_0)) = k2_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_37]),c_0_38]),c_0_27])])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 != k2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_73,negated_conjecture,
    ( esk2_0 = k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0)) = k2_funct_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_46]),c_0_38]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.63/0.78  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.63/0.78  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.63/0.78  #
% 0.63/0.78  # Preprocessing time       : 0.027 s
% 0.63/0.78  
% 0.63/0.78  # Proof found!
% 0.63/0.78  # SZS status Theorem
% 0.63/0.78  # SZS output start CNFRefutation
% 0.63/0.78  fof(t64_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 0.63/0.78  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.63/0.78  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.63/0.78  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.63/0.78  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.63/0.78  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 0.63/0.78  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 0.63/0.78  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.63/0.78  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.63/0.78  fof(t44_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 0.63/0.78  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.63/0.78  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.63/0.78  fof(c_0_12, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1))))), inference(assume_negation,[status(cth)],[t64_funct_1])).
% 0.63/0.78  fof(c_0_13, plain, ![X6]:(~v1_relat_1(X6)|k10_relat_1(X6,k2_relat_1(X6))=k1_relat_1(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.63/0.78  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(((v2_funct_1(esk1_0)&k2_relat_1(esk2_0)=k1_relat_1(esk1_0))&k5_relat_1(esk2_0,esk1_0)=k6_relat_1(k2_relat_1(esk1_0)))&esk2_0!=k2_funct_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.63/0.78  fof(c_0_15, plain, ![X7, X8]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|k1_relat_1(k5_relat_1(X7,X8))=k10_relat_1(X7,k1_relat_1(X8)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.63/0.78  cnf(c_0_16, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.63/0.78  cnf(c_0_17, negated_conjecture, (k2_relat_1(esk2_0)=k1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  fof(c_0_19, plain, ![X12]:(k1_relat_1(k6_relat_1(X12))=X12&k2_relat_1(k6_relat_1(X12))=X12), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.63/0.78  fof(c_0_20, plain, ![X4, X5]:(~v1_relat_1(X4)|~v1_relat_1(X5)|v1_relat_1(k5_relat_1(X4,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.63/0.78  fof(c_0_21, plain, ![X9, X10, X11]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~v1_relat_1(X11)|k5_relat_1(k5_relat_1(X9,X10),X11)=k5_relat_1(X9,k5_relat_1(X10,X11))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.63/0.78  fof(c_0_22, plain, ![X13]:(~v1_relat_1(X13)|k5_relat_1(k6_relat_1(k1_relat_1(X13)),X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.63/0.78  cnf(c_0_23, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.63/0.78  cnf(c_0_24, negated_conjecture, (k10_relat_1(esk2_0,k1_relat_1(esk1_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.63/0.78  cnf(c_0_25, negated_conjecture, (k5_relat_1(esk2_0,esk1_0)=k6_relat_1(k2_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  cnf(c_0_26, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.78  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  cnf(c_0_28, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.78  cnf(c_0_29, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.63/0.78  cnf(c_0_30, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.78  cnf(c_0_31, negated_conjecture, (k1_relat_1(esk2_0)=k2_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_18])])).
% 0.63/0.78  fof(c_0_32, plain, ![X20]:((k5_relat_1(X20,k2_funct_1(X20))=k6_relat_1(k1_relat_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(k5_relat_1(k2_funct_1(X20),X20)=k6_relat_1(k2_relat_1(X20))|~v2_funct_1(X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.63/0.78  cnf(c_0_33, plain, (v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_28])).
% 0.63/0.78  cnf(c_0_34, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_18])])).
% 0.63/0.78  cnf(c_0_35, negated_conjecture, (v1_relat_1(k6_relat_1(k2_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_27]), c_0_18])])).
% 0.63/0.78  cnf(c_0_36, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.63/0.78  cnf(c_0_37, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  cnf(c_0_39, negated_conjecture, (k10_relat_1(X1,k2_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_31]), c_0_18])])).
% 0.63/0.78  cnf(c_0_40, negated_conjecture, (v1_relat_1(k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_18]), c_0_35])])).
% 0.63/0.78  cnf(c_0_41, negated_conjecture, (k5_relat_1(esk1_0,k2_funct_1(esk1_0))=k6_relat_1(k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_27])])).
% 0.63/0.78  fof(c_0_42, plain, ![X14]:((v1_relat_1(k2_funct_1(X14))|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(v1_funct_1(k2_funct_1(X14))|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.63/0.78  cnf(c_0_43, plain, (k10_relat_1(X1,X2)=k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(k6_relat_1(X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_26])).
% 0.63/0.78  cnf(c_0_44, negated_conjecture, (k10_relat_1(X1,k10_relat_1(X2,k2_relat_1(esk1_0)))=k1_relat_1(k5_relat_1(X1,k5_relat_1(X2,esk2_0)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_39]), c_0_40])).
% 0.63/0.78  cnf(c_0_45, negated_conjecture, (v1_relat_1(k6_relat_1(k1_relat_1(esk1_0)))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_41]), c_0_27])])).
% 0.63/0.78  cnf(c_0_46, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.63/0.78  cnf(c_0_47, negated_conjecture, (k1_relat_1(k5_relat_1(X1,esk2_0))=k1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(esk1_0))))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_39]), c_0_35])])).
% 0.63/0.78  fof(c_0_48, plain, ![X17, X18]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18)|(k2_relat_1(X17)!=k1_relat_1(X18)|k5_relat_1(X17,X18)!=X17|X18=k6_relat_1(k1_relat_1(X18))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).
% 0.63/0.78  cnf(c_0_49, negated_conjecture, (k10_relat_1(X1,k1_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,k5_relat_1(esk1_0,esk2_0)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_27])])).
% 0.63/0.78  cnf(c_0_50, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),k5_relat_1(X1,X2))=k5_relat_1(X1,X2)|~v1_relat_1(k6_relat_1(k1_relat_1(X1)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.63/0.78  cnf(c_0_51, negated_conjecture, (v1_relat_1(k6_relat_1(k1_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_38]), c_0_27])])).
% 0.63/0.78  cnf(c_0_52, negated_conjecture, (k10_relat_1(X1,k2_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,k6_relat_1(k2_relat_1(esk1_0))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_47])).
% 0.63/0.78  cnf(c_0_53, negated_conjecture, (k5_relat_1(k6_relat_1(k10_relat_1(X1,k2_relat_1(esk1_0))),k5_relat_1(X1,esk2_0))=k5_relat_1(X1,esk2_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_39]), c_0_40])).
% 0.63/0.78  cnf(c_0_54, plain, (X2=k6_relat_1(k1_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.63/0.78  cnf(c_0_55, negated_conjecture, (k5_relat_1(esk2_0,k5_relat_1(esk1_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_27]), c_0_18])])).
% 0.63/0.78  cnf(c_0_56, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  cnf(c_0_57, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,esk2_0))=k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_18]), c_0_27])])).
% 0.63/0.78  cnf(c_0_58, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,k6_relat_1(k2_relat_1(esk1_0))))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_52]), c_0_27])])).
% 0.63/0.78  cnf(c_0_59, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,esk2_0))=k5_relat_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_16]), c_0_27])])).
% 0.63/0.78  cnf(c_0_60, negated_conjecture, (k6_relat_1(k1_relat_1(k5_relat_1(esk1_0,X1)))=k5_relat_1(esk1_0,X1)|k1_relat_1(k5_relat_1(esk1_0,X1))!=k1_relat_1(esk1_0)|k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1)!=esk2_0|~v1_funct_1(k5_relat_1(esk1_0,X1))|~v1_relat_1(k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_17]), c_0_56]), c_0_18])])).
% 0.63/0.78  cnf(c_0_61, negated_conjecture, (k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_57]), c_0_58]), c_0_27])])).
% 0.63/0.78  cnf(c_0_62, negated_conjecture, (v1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_59]), c_0_18]), c_0_27]), c_0_51])])).
% 0.63/0.78  fof(c_0_63, plain, ![X15, X16]:((v1_relat_1(k5_relat_1(X15,X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v1_relat_1(X16)|~v1_funct_1(X16)))&(v1_funct_1(k5_relat_1(X15,X16))|(~v1_relat_1(X15)|~v1_funct_1(X15)|~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.63/0.78  cnf(c_0_64, negated_conjecture, (k5_relat_1(esk1_0,esk2_0)=k6_relat_1(k1_relat_1(esk1_0))|~v1_funct_1(k5_relat_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_34]), c_0_57]), c_0_61]), c_0_57]), c_0_61]), c_0_62]), c_0_18])])).
% 0.63/0.78  cnf(c_0_65, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.63/0.78  fof(c_0_66, plain, ![X19]:((k2_relat_1(X19)=k1_relat_1(k2_funct_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k1_relat_1(X19)=k2_relat_1(k2_funct_1(X19))|~v2_funct_1(X19)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.63/0.78  cnf(c_0_67, negated_conjecture, (k5_relat_1(esk1_0,esk2_0)=k6_relat_1(k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_56]), c_0_38]), c_0_18]), c_0_27])])).
% 0.63/0.78  cnf(c_0_68, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.63/0.78  cnf(c_0_69, negated_conjecture, (k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk1_0)))=k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_41])).
% 0.63/0.78  cnf(c_0_70, negated_conjecture, (k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk1_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_67]), c_0_34]), c_0_18])])).
% 0.63/0.78  cnf(c_0_71, negated_conjecture, (k1_relat_1(k2_funct_1(esk1_0))=k2_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_37]), c_0_38]), c_0_27])])).
% 0.63/0.78  cnf(c_0_72, negated_conjecture, (esk2_0!=k2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.63/0.78  cnf(c_0_73, negated_conjecture, (esk2_0=k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.63/0.78  cnf(c_0_74, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0))=k2_funct_1(esk1_0)|~v1_relat_1(k2_funct_1(esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_71])).
% 0.63/0.78  cnf(c_0_75, negated_conjecture, (~v1_relat_1(k2_funct_1(esk1_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74])).
% 0.63/0.78  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_46]), c_0_38]), c_0_27])]), ['proof']).
% 0.63/0.78  # SZS output end CNFRefutation
% 0.63/0.78  # Proof object total steps             : 77
% 0.63/0.78  # Proof object clause steps            : 52
% 0.63/0.78  # Proof object formula steps           : 25
% 0.63/0.78  # Proof object conjectures             : 41
% 0.63/0.78  # Proof object clause conjectures      : 38
% 0.63/0.78  # Proof object formula conjectures     : 3
% 0.63/0.78  # Proof object initial clauses used    : 19
% 0.63/0.78  # Proof object initial formulas used   : 12
% 0.63/0.78  # Proof object generating inferences   : 33
% 0.63/0.78  # Proof object simplifying inferences  : 76
% 0.63/0.78  # Training examples: 0 positive, 0 negative
% 0.63/0.78  # Parsed axioms                        : 12
% 0.63/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.63/0.78  # Initial clauses                      : 24
% 0.63/0.78  # Removed in clause preprocessing      : 0
% 0.63/0.78  # Initial clauses in saturation        : 24
% 0.63/0.78  # Processed clauses                    : 2629
% 0.63/0.78  # ...of these trivial                  : 65
% 0.63/0.78  # ...subsumed                          : 1822
% 0.63/0.78  # ...remaining for further processing  : 742
% 0.63/0.78  # Other redundant clauses eliminated   : 18
% 0.63/0.78  # Clauses deleted for lack of memory   : 0
% 0.63/0.78  # Backward-subsumed                    : 31
% 0.63/0.78  # Backward-rewritten                   : 125
% 0.63/0.78  # Generated clauses                    : 33794
% 0.63/0.78  # ...of the previous two non-trivial   : 31647
% 0.63/0.78  # Contextual simplify-reflections      : 158
% 0.63/0.78  # Paramodulations                      : 33776
% 0.63/0.78  # Factorizations                       : 0
% 0.63/0.78  # Equation resolutions                 : 18
% 0.63/0.78  # Propositional unsat checks           : 0
% 0.63/0.78  #    Propositional check models        : 0
% 0.63/0.78  #    Propositional check unsatisfiable : 0
% 0.63/0.78  #    Propositional clauses             : 0
% 0.63/0.78  #    Propositional clauses after purity: 0
% 0.63/0.78  #    Propositional unsat core size     : 0
% 0.63/0.78  #    Propositional preprocessing time  : 0.000
% 0.63/0.78  #    Propositional encoding time       : 0.000
% 0.63/0.78  #    Propositional solver time         : 0.000
% 0.63/0.78  #    Success case prop preproc time    : 0.000
% 0.63/0.78  #    Success case prop encoding time   : 0.000
% 0.63/0.78  #    Success case prop solver time     : 0.000
% 0.63/0.78  # Current number of processed clauses  : 586
% 0.63/0.78  #    Positive orientable unit clauses  : 124
% 0.63/0.78  #    Positive unorientable unit clauses: 0
% 0.63/0.78  #    Negative unit clauses             : 2
% 0.63/0.78  #    Non-unit-clauses                  : 460
% 0.63/0.78  # Current number of unprocessed clauses: 28962
% 0.63/0.78  # ...number of literals in the above   : 184774
% 0.63/0.78  # Current number of archived formulas  : 0
% 0.63/0.78  # Current number of archived clauses   : 156
% 0.63/0.78  # Clause-clause subsumption calls (NU) : 48681
% 0.63/0.78  # Rec. Clause-clause subsumption calls : 36317
% 0.63/0.78  # Non-unit clause-clause subsumptions  : 2002
% 0.63/0.78  # Unit Clause-clause subsumption calls : 660
% 0.63/0.78  # Rewrite failures with RHS unbound    : 0
% 0.63/0.78  # BW rewrite match attempts            : 2101
% 0.63/0.78  # BW rewrite match successes           : 25
% 0.63/0.78  # Condensation attempts                : 0
% 0.63/0.78  # Condensation successes               : 0
% 0.63/0.78  # Termbank termtop insertions          : 908193
% 0.63/0.79  
% 0.63/0.79  # -------------------------------------------------
% 0.63/0.79  # User time                : 0.420 s
% 0.63/0.79  # System time              : 0.024 s
% 0.63/0.79  # Total time               : 0.444 s
% 0.63/0.79  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
