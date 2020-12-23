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
% DateTime   : Thu Dec  3 10:54:05 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  111 (1549 expanded)
%              Number of clauses        :   82 ( 539 expanded)
%              Number of leaves         :   14 ( 392 expanded)
%              Depth                    :   20
%              Number of atoms          :  303 (7544 expanded)
%              Number of equality atoms :   90 (2592 expanded)
%              Maximal formula depth    :   10 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(t78_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | v1_relat_1(k5_relat_1(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_16,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | k5_relat_1(k5_relat_1(X11,X12),X13) = k5_relat_1(X11,k5_relat_1(X12,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_17,plain,(
    ! [X22] :
      ( ( k5_relat_1(X22,k2_funct_1(X22)) = k6_relat_1(k1_relat_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k5_relat_1(k2_funct_1(X22),X22) = k6_relat_1(k2_relat_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk1_0)
    & k2_relat_1(esk2_0) = k1_relat_1(esk1_0)
    & k5_relat_1(esk2_0,esk1_0) = k6_relat_1(k2_relat_1(esk1_0))
    & esk2_0 != k2_funct_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(esk1_0,k2_funct_1(esk1_0)) = k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])])).

fof(c_0_27,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | k1_relat_1(k5_relat_1(X8,X9)) = k10_relat_1(X8,k1_relat_1(X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_28,plain,(
    ! [X10] :
      ( ( k2_relat_1(X10) = k1_relat_1(k4_relat_1(X10))
        | ~ v1_relat_1(X10) )
      & ( k1_relat_1(X10) = k2_relat_1(k4_relat_1(X10))
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_29,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | v1_relat_1(k4_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_30,plain,
    ( v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,k5_relat_1(X3,X4))))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( k5_relat_1(esk1_0,k5_relat_1(k2_funct_1(esk1_0),X1)) = k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),X1)
    | ~ v1_relat_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_24])])).

fof(c_0_32,plain,(
    ! [X17] :
      ( ( v1_relat_1(k2_funct_1(X17))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( v1_funct_1(k2_funct_1(X17))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_33,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k10_relat_1(X7,k2_relat_1(X7)) = k1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_34,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),X2)))
    | ~ v1_relat_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])])).

cnf(c_0_38,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_39,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k6_relat_1(k1_relat_1(X15)),X15) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk2_0) = k1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_43,plain,(
    ! [X14] :
      ( k1_relat_1(k6_relat_1(X14)) = X14
      & k2_relat_1(k6_relat_1(X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_44,plain,
    ( k10_relat_1(X1,k2_relat_1(X2)) = k1_relat_1(k5_relat_1(X1,k4_relat_1(X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_23]),c_0_24])])).

cnf(c_0_46,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_relat_1(esk1_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_48,negated_conjecture,
    ( k5_relat_1(esk2_0,esk1_0) = k6_relat_1(k2_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(X1,k1_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_41]),c_0_42])])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_24])])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk2_0) = k2_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_47]),c_0_48]),c_0_49]),c_0_24]),c_0_42])])).

cnf(c_0_53,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0))) = k1_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_24])])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(k6_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_26]),c_0_24])])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,esk1_0)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_20]),c_0_24])]),c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(X1,k2_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_52]),c_0_42])])).

cnf(c_0_58,plain,
    ( k10_relat_1(k6_relat_1(X1),X1) = X1
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_53]),c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( k10_relat_1(X1,k1_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( v1_relat_1(k6_relat_1(k1_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_38]),c_0_23]),c_0_24])])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_31]),c_0_24])])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,esk2_0)) = k1_relat_1(k5_relat_1(X1,k4_relat_1(esk1_0)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_24])])).

fof(c_0_63,plain,(
    ! [X18,X19] :
      ( ( v1_relat_1(k5_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( v1_funct_1(k5_relat_1(X18,X19))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_38]),c_0_23]),c_0_24])])).

cnf(c_0_66,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_52]),c_0_42])])).

cnf(c_0_67,negated_conjecture,
    ( v1_relat_1(k6_relat_1(k2_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_48]),c_0_24]),c_0_42])])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(X1,k2_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,k4_relat_1(esk1_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_62])).

cnf(c_0_69,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)) = k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_64]),c_0_65])])).

cnf(c_0_71,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1)) = k4_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_36])).

cnf(c_0_72,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_66]),c_0_42]),c_0_67])])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,k4_relat_1(esk1_0))) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_68]),c_0_24])])).

fof(c_0_74,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | ~ v2_funct_1(X16)
      | k2_funct_1(X16) = k4_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(k6_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_funct_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_26]),c_0_23]),c_0_24])])).

cnf(c_0_76,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_46]),c_0_24])])).

cnf(c_0_78,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k4_relat_1(esk2_0)) = k4_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_42])])).

cnf(c_0_79,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k10_relat_1(X1,k2_relat_1(esk1_0))),k5_relat_1(X1,esk2_0)) = k5_relat_1(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_57]),c_0_72])).

cnf(c_0_80,plain,
    ( v1_funct_1(k5_relat_1(X1,k5_relat_1(X2,X3)))
    | ~ v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_20]),c_0_19])).

cnf(c_0_81,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,k4_relat_1(esk1_0))) = k5_relat_1(esk1_0,k4_relat_1(esk1_0))
    | ~ v1_relat_1(k5_relat_1(esk1_0,k4_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_73])).

cnf(c_0_82,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_1(k6_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_23]),c_0_24])])).

fof(c_0_84,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | k2_relat_1(X20) != k1_relat_1(X21)
      | k5_relat_1(X20,X21) != X20
      | X21 = k6_relat_1(k1_relat_1(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,X1)) = k5_relat_1(esk1_0,X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_77]),c_0_24]),c_0_60])])).

cnf(c_0_86,negated_conjecture,
    ( k10_relat_1(X1,k10_relat_1(X2,k2_relat_1(esk1_0))) = k1_relat_1(k5_relat_1(X1,k5_relat_1(X2,esk2_0)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_57]),c_0_72])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk2_0)) = k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_78]),c_0_60])])).

cnf(c_0_88,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,esk2_0)) = k5_relat_1(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_40]),c_0_24])])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_90,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(k5_relat_1(X1,k6_relat_1(k1_relat_1(X2))))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_46])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k6_relat_1(k1_relat_1(esk1_0))) = k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_26]),c_0_26]),c_0_26]),c_0_60]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_1(k6_relat_1(k1_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_38]),c_0_23]),c_0_24])])).

cnf(c_0_93,plain,
    ( X2 = k6_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( k5_relat_1(esk2_0,k5_relat_1(esk1_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_48]),c_0_24]),c_0_42])])).

cnf(c_0_95,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_85]),c_0_24]),c_0_60])])).

cnf(c_0_96,negated_conjecture,
    ( k10_relat_1(X1,k1_relat_1(esk1_0)) = k1_relat_1(k5_relat_1(X1,k5_relat_1(esk1_0,esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_40]),c_0_24])])).

cnf(c_0_97,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X1)),k5_relat_1(X1,X2)) = k5_relat_1(X1,X2)
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(X1)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_46])).

cnf(c_0_98,negated_conjecture,
    ( k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_87]),c_0_41]),c_0_42])])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk1_0,esk2_0))
    | ~ v1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_88]),c_0_89]),c_0_42]),c_0_24]),c_0_60])])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_23]),c_0_60]),c_0_24])])).

cnf(c_0_101,negated_conjecture,
    ( k6_relat_1(k1_relat_1(k5_relat_1(esk1_0,X1))) = k5_relat_1(esk1_0,X1)
    | k1_relat_1(k5_relat_1(esk1_0,X1)) != k1_relat_1(esk1_0)
    | k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1) != esk2_0
    | ~ v1_funct_1(k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_41]),c_0_89]),c_0_42])]),c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk1_0,esk2_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_60]),c_0_42]),c_0_24])])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( k5_relat_1(esk1_0,esk2_0) = k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_66]),c_0_102]),c_0_102]),c_0_103]),c_0_42])])).

cnf(c_0_105,plain,
    ( k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1)) = k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_82])).

cnf(c_0_106,negated_conjecture,
    ( k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk1_0))) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_104]),c_0_66]),c_0_42])])).

cnf(c_0_107,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0)) = k2_funct_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_108,negated_conjecture,
    ( esk2_0 != k2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_26]),c_0_106]),c_0_107]),c_0_108])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_38]),c_0_23]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n007.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:46:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.47/0.65  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.47/0.65  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.65  #
% 0.47/0.65  # Preprocessing time       : 0.027 s
% 0.47/0.65  
% 0.47/0.65  # Proof found!
% 0.47/0.65  # SZS status Theorem
% 0.47/0.65  # SZS output start CNFRefutation
% 0.47/0.65  fof(t64_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 0.47/0.65  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.47/0.65  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.47/0.65  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.47/0.65  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.47/0.65  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.47/0.65  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.47/0.65  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.47/0.65  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.47/0.65  fof(t78_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 0.47/0.65  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.47/0.65  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.47/0.65  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 0.47/0.65  fof(t44_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 0.47/0.65  fof(c_0_14, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X2)=k1_relat_1(X1))&k5_relat_1(X2,X1)=k6_relat_1(k2_relat_1(X1)))=>X2=k2_funct_1(X1))))), inference(assume_negation,[status(cth)],[t64_funct_1])).
% 0.47/0.65  fof(c_0_15, plain, ![X5, X6]:(~v1_relat_1(X5)|~v1_relat_1(X6)|v1_relat_1(k5_relat_1(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.47/0.65  fof(c_0_16, plain, ![X11, X12, X13]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|(~v1_relat_1(X13)|k5_relat_1(k5_relat_1(X11,X12),X13)=k5_relat_1(X11,k5_relat_1(X12,X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.47/0.65  fof(c_0_17, plain, ![X22]:((k5_relat_1(X22,k2_funct_1(X22))=k6_relat_1(k1_relat_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k5_relat_1(k2_funct_1(X22),X22)=k6_relat_1(k2_relat_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.47/0.65  fof(c_0_18, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(((v2_funct_1(esk1_0)&k2_relat_1(esk2_0)=k1_relat_1(esk1_0))&k5_relat_1(esk2_0,esk1_0)=k6_relat_1(k2_relat_1(esk1_0)))&esk2_0!=k2_funct_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.47/0.65  cnf(c_0_19, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.65  cnf(c_0_20, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.65  cnf(c_0_21, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.65  cnf(c_0_22, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_25, plain, (v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,X3)))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_19])).
% 0.47/0.65  cnf(c_0_26, negated_conjecture, (k5_relat_1(esk1_0,k2_funct_1(esk1_0))=k6_relat_1(k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])])).
% 0.47/0.65  fof(c_0_27, plain, ![X8, X9]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|k1_relat_1(k5_relat_1(X8,X9))=k10_relat_1(X8,k1_relat_1(X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.47/0.65  fof(c_0_28, plain, ![X10]:((k2_relat_1(X10)=k1_relat_1(k4_relat_1(X10))|~v1_relat_1(X10))&(k1_relat_1(X10)=k2_relat_1(k4_relat_1(X10))|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.47/0.65  fof(c_0_29, plain, ![X4]:(~v1_relat_1(X4)|v1_relat_1(k4_relat_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.47/0.65  cnf(c_0_30, plain, (v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,k5_relat_1(X3,X4))))|~v1_relat_1(X4)|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_19])).
% 0.47/0.65  cnf(c_0_31, negated_conjecture, (k5_relat_1(esk1_0,k5_relat_1(k2_funct_1(esk1_0),X1))=k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),X1)|~v1_relat_1(k2_funct_1(esk1_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_26]), c_0_24])])).
% 0.47/0.65  fof(c_0_32, plain, ![X17]:((v1_relat_1(k2_funct_1(X17))|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(v1_funct_1(k2_funct_1(X17))|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.47/0.65  fof(c_0_33, plain, ![X7]:(~v1_relat_1(X7)|k10_relat_1(X7,k2_relat_1(X7))=k1_relat_1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.47/0.65  cnf(c_0_34, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.65  cnf(c_0_35, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.65  cnf(c_0_36, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.47/0.65  cnf(c_0_37, negated_conjecture, (v1_relat_1(k5_relat_1(X1,k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),X2)))|~v1_relat_1(k2_funct_1(esk1_0))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])])).
% 0.47/0.65  cnf(c_0_38, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.65  fof(c_0_39, plain, ![X15]:(~v1_relat_1(X15)|k5_relat_1(k6_relat_1(k1_relat_1(X15)),X15)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t78_relat_1])])).
% 0.47/0.65  cnf(c_0_40, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.65  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk2_0)=k1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  fof(c_0_43, plain, ![X14]:(k1_relat_1(k6_relat_1(X14))=X14&k2_relat_1(k6_relat_1(X14))=X14), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.47/0.65  cnf(c_0_44, plain, (k10_relat_1(X1,k2_relat_1(X2))=k1_relat_1(k5_relat_1(X1,k4_relat_1(X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.47/0.65  cnf(c_0_45, negated_conjecture, (v1_relat_1(k5_relat_1(X1,k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_23]), c_0_24])])).
% 0.47/0.65  cnf(c_0_46, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),X1)=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.65  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk2_0,k1_relat_1(esk1_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.47/0.65  cnf(c_0_48, negated_conjecture, (k5_relat_1(esk2_0,esk1_0)=k6_relat_1(k2_relat_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_49, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.65  cnf(c_0_50, negated_conjecture, (k10_relat_1(X1,k1_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_41]), c_0_42])])).
% 0.47/0.65  cnf(c_0_51, negated_conjecture, (v1_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_24])])).
% 0.47/0.65  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk2_0)=k2_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_47]), c_0_48]), c_0_49]), c_0_24]), c_0_42])])).
% 0.47/0.65  cnf(c_0_53, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.47/0.65  cnf(c_0_54, negated_conjecture, (k1_relat_1(k5_relat_1(X1,k4_relat_1(esk2_0)))=k1_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_50]), c_0_24])])).
% 0.47/0.65  cnf(c_0_55, negated_conjecture, (v1_relat_1(k6_relat_1(k1_relat_1(esk1_0)))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_26]), c_0_24])])).
% 0.47/0.65  cnf(c_0_56, negated_conjecture, (v1_relat_1(k5_relat_1(X1,k5_relat_1(X2,esk1_0)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_20]), c_0_24])]), c_0_19])).
% 0.47/0.65  cnf(c_0_57, negated_conjecture, (k10_relat_1(X1,k2_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_52]), c_0_42])])).
% 0.47/0.65  cnf(c_0_58, plain, (k10_relat_1(k6_relat_1(X1),X1)=X1|~v1_relat_1(k6_relat_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_53]), c_0_49])).
% 0.47/0.65  cnf(c_0_59, negated_conjecture, (k10_relat_1(X1,k1_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,esk1_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_54])).
% 0.47/0.65  cnf(c_0_60, negated_conjecture, (v1_relat_1(k6_relat_1(k1_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_38]), c_0_23]), c_0_24])])).
% 0.47/0.65  cnf(c_0_61, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_31]), c_0_24])])).
% 0.47/0.65  cnf(c_0_62, negated_conjecture, (k1_relat_1(k5_relat_1(X1,esk2_0))=k1_relat_1(k5_relat_1(X1,k4_relat_1(esk1_0)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_44]), c_0_24])])).
% 0.47/0.65  fof(c_0_63, plain, ![X18, X19]:((v1_relat_1(k5_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)|~v1_relat_1(X19)|~v1_funct_1(X19)))&(v1_funct_1(k5_relat_1(X18,X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)|~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.47/0.65  cnf(c_0_64, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.47/0.65  cnf(c_0_65, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_38]), c_0_23]), c_0_24])])).
% 0.47/0.65  cnf(c_0_66, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_52]), c_0_42])])).
% 0.47/0.65  cnf(c_0_67, negated_conjecture, (v1_relat_1(k6_relat_1(k2_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_48]), c_0_24]), c_0_42])])).
% 0.47/0.65  cnf(c_0_68, negated_conjecture, (k10_relat_1(X1,k2_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,k4_relat_1(esk1_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_57, c_0_62])).
% 0.47/0.65  cnf(c_0_69, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.47/0.65  cnf(c_0_70, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))=k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_64]), c_0_65])])).
% 0.47/0.65  cnf(c_0_71, plain, (k5_relat_1(k6_relat_1(k2_relat_1(X1)),k4_relat_1(X1))=k4_relat_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_36])).
% 0.47/0.65  cnf(c_0_72, negated_conjecture, (v1_relat_1(k5_relat_1(X1,esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_66]), c_0_42]), c_0_67])])).
% 0.47/0.65  cnf(c_0_73, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,k4_relat_1(esk1_0)))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_68]), c_0_24])])).
% 0.47/0.65  fof(c_0_74, plain, ![X16]:(~v1_relat_1(X16)|~v1_funct_1(X16)|(~v2_funct_1(X16)|k2_funct_1(X16)=k4_relat_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.47/0.65  cnf(c_0_75, negated_conjecture, (v1_funct_1(k6_relat_1(k1_relat_1(esk1_0)))|~v1_funct_1(k2_funct_1(esk1_0))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_26]), c_0_23]), c_0_24])])).
% 0.47/0.65  cnf(c_0_76, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.65  cnf(c_0_77, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_46]), c_0_24])])).
% 0.47/0.65  cnf(c_0_78, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k4_relat_1(esk2_0))=k4_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_41]), c_0_42])])).
% 0.47/0.65  cnf(c_0_79, negated_conjecture, (k5_relat_1(k6_relat_1(k10_relat_1(X1,k2_relat_1(esk1_0))),k5_relat_1(X1,esk2_0))=k5_relat_1(X1,esk2_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_57]), c_0_72])).
% 0.47/0.65  cnf(c_0_80, plain, (v1_funct_1(k5_relat_1(X1,k5_relat_1(X2,X3)))|~v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(X3)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_20]), c_0_19])).
% 0.47/0.65  cnf(c_0_81, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,k4_relat_1(esk1_0)))=k5_relat_1(esk1_0,k4_relat_1(esk1_0))|~v1_relat_1(k5_relat_1(esk1_0,k4_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_46, c_0_73])).
% 0.47/0.65  cnf(c_0_82, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.47/0.65  cnf(c_0_83, negated_conjecture, (v1_funct_1(k6_relat_1(k1_relat_1(esk1_0)))|~v1_relat_1(k2_funct_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_23]), c_0_24])])).
% 0.47/0.65  fof(c_0_84, plain, ![X20, X21]:(~v1_relat_1(X20)|~v1_funct_1(X20)|(~v1_relat_1(X21)|~v1_funct_1(X21)|(k2_relat_1(X20)!=k1_relat_1(X21)|k5_relat_1(X20,X21)!=X20|X21=k6_relat_1(k1_relat_1(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).
% 0.47/0.65  cnf(c_0_85, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,X1))=k5_relat_1(esk1_0,X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_77]), c_0_24]), c_0_60])])).
% 0.47/0.65  cnf(c_0_86, negated_conjecture, (k10_relat_1(X1,k10_relat_1(X2,k2_relat_1(esk1_0)))=k1_relat_1(k5_relat_1(X1,k5_relat_1(X2,esk2_0)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_57]), c_0_72])).
% 0.47/0.65  cnf(c_0_87, negated_conjecture, (k1_relat_1(k4_relat_1(esk2_0))=k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_78]), c_0_60])])).
% 0.47/0.65  cnf(c_0_88, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k5_relat_1(esk1_0,esk2_0))=k5_relat_1(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_40]), c_0_24])])).
% 0.47/0.65  cnf(c_0_89, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_90, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_funct_1(k5_relat_1(X1,k6_relat_1(k1_relat_1(X2))))|~v1_funct_1(X2)|~v1_relat_1(k6_relat_1(k1_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_80, c_0_46])).
% 0.47/0.65  cnf(c_0_91, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k6_relat_1(k1_relat_1(esk1_0)))=k6_relat_1(k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_26]), c_0_26]), c_0_26]), c_0_60]), c_0_22]), c_0_23]), c_0_24])])).
% 0.47/0.65  cnf(c_0_92, negated_conjecture, (v1_funct_1(k6_relat_1(k1_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_38]), c_0_23]), c_0_24])])).
% 0.47/0.65  cnf(c_0_93, plain, (X2=k6_relat_1(k1_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.47/0.65  cnf(c_0_94, negated_conjecture, (k5_relat_1(esk2_0,k5_relat_1(esk1_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_48]), c_0_24]), c_0_42])])).
% 0.47/0.65  cnf(c_0_95, negated_conjecture, (v1_relat_1(k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_85]), c_0_24]), c_0_60])])).
% 0.47/0.65  cnf(c_0_96, negated_conjecture, (k10_relat_1(X1,k1_relat_1(esk1_0))=k1_relat_1(k5_relat_1(X1,k5_relat_1(esk1_0,esk2_0)))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_40]), c_0_24])])).
% 0.47/0.65  cnf(c_0_97, plain, (k5_relat_1(k6_relat_1(k1_relat_1(X1)),k5_relat_1(X1,X2))=k5_relat_1(X1,X2)|~v1_relat_1(k6_relat_1(k1_relat_1(X1)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_46])).
% 0.47/0.65  cnf(c_0_98, negated_conjecture, (k10_relat_1(k6_relat_1(k1_relat_1(esk1_0)),k1_relat_1(esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_87]), c_0_41]), c_0_42])])).
% 0.47/0.65  cnf(c_0_99, negated_conjecture, (v1_funct_1(k5_relat_1(esk1_0,esk2_0))|~v1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_88]), c_0_89]), c_0_42]), c_0_24]), c_0_60])])).
% 0.47/0.65  cnf(c_0_100, negated_conjecture, (v1_funct_1(k5_relat_1(k6_relat_1(k1_relat_1(esk1_0)),esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_23]), c_0_60]), c_0_24])])).
% 0.47/0.65  cnf(c_0_101, negated_conjecture, (k6_relat_1(k1_relat_1(k5_relat_1(esk1_0,X1)))=k5_relat_1(esk1_0,X1)|k1_relat_1(k5_relat_1(esk1_0,X1))!=k1_relat_1(esk1_0)|k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),X1)!=esk2_0|~v1_funct_1(k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_41]), c_0_89]), c_0_42])]), c_0_95])).
% 0.47/0.65  cnf(c_0_102, negated_conjecture, (k1_relat_1(k5_relat_1(esk1_0,esk2_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_60]), c_0_42]), c_0_24])])).
% 0.47/0.65  cnf(c_0_103, negated_conjecture, (v1_funct_1(k5_relat_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_100])])).
% 0.47/0.65  cnf(c_0_104, negated_conjecture, (k5_relat_1(esk1_0,esk2_0)=k6_relat_1(k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_66]), c_0_102]), c_0_102]), c_0_103]), c_0_42])])).
% 0.47/0.65  cnf(c_0_105, plain, (k5_relat_1(k6_relat_1(k2_relat_1(X1)),k2_funct_1(X1))=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_71, c_0_82])).
% 0.47/0.65  cnf(c_0_106, negated_conjecture, (k5_relat_1(esk2_0,k6_relat_1(k1_relat_1(esk1_0)))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_104]), c_0_66]), c_0_42])])).
% 0.47/0.65  cnf(c_0_107, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk1_0)),k2_funct_1(esk1_0))=k2_funct_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_22]), c_0_23]), c_0_24])])).
% 0.47/0.65  cnf(c_0_108, negated_conjecture, (esk2_0!=k2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.65  cnf(c_0_109, negated_conjecture, (~v1_relat_1(k2_funct_1(esk1_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_26]), c_0_106]), c_0_107]), c_0_108])).
% 0.47/0.65  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_38]), c_0_23]), c_0_24])]), ['proof']).
% 0.47/0.65  # SZS output end CNFRefutation
% 0.47/0.65  # Proof object total steps             : 111
% 0.47/0.65  # Proof object clause steps            : 82
% 0.47/0.65  # Proof object formula steps           : 29
% 0.47/0.65  # Proof object conjectures             : 61
% 0.47/0.65  # Proof object clause conjectures      : 58
% 0.47/0.65  # Proof object formula conjectures     : 3
% 0.47/0.65  # Proof object initial clauses used    : 23
% 0.47/0.65  # Proof object initial formulas used   : 14
% 0.47/0.65  # Proof object generating inferences   : 58
% 0.47/0.65  # Proof object simplifying inferences  : 140
% 0.47/0.65  # Training examples: 0 positive, 0 negative
% 0.47/0.65  # Parsed axioms                        : 14
% 0.47/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.65  # Initial clauses                      : 26
% 0.47/0.65  # Removed in clause preprocessing      : 0
% 0.47/0.65  # Initial clauses in saturation        : 26
% 0.47/0.65  # Processed clauses                    : 1794
% 0.47/0.65  # ...of these trivial                  : 40
% 0.47/0.65  # ...subsumed                          : 1056
% 0.47/0.65  # ...remaining for further processing  : 698
% 0.47/0.65  # Other redundant clauses eliminated   : 6
% 0.47/0.65  # Clauses deleted for lack of memory   : 0
% 0.47/0.65  # Backward-subsumed                    : 36
% 0.47/0.65  # Backward-rewritten                   : 130
% 0.47/0.65  # Generated clauses                    : 23043
% 0.47/0.65  # ...of the previous two non-trivial   : 21382
% 0.47/0.65  # Contextual simplify-reflections      : 102
% 0.47/0.65  # Paramodulations                      : 23037
% 0.47/0.65  # Factorizations                       : 0
% 0.47/0.65  # Equation resolutions                 : 6
% 0.47/0.65  # Propositional unsat checks           : 0
% 0.47/0.65  #    Propositional check models        : 0
% 0.47/0.65  #    Propositional check unsatisfiable : 0
% 0.47/0.65  #    Propositional clauses             : 0
% 0.47/0.65  #    Propositional clauses after purity: 0
% 0.47/0.65  #    Propositional unsat core size     : 0
% 0.47/0.65  #    Propositional preprocessing time  : 0.000
% 0.47/0.65  #    Propositional encoding time       : 0.000
% 0.47/0.65  #    Propositional solver time         : 0.000
% 0.47/0.65  #    Success case prop preproc time    : 0.000
% 0.47/0.65  #    Success case prop encoding time   : 0.000
% 0.47/0.65  #    Success case prop solver time     : 0.000
% 0.47/0.65  # Current number of processed clauses  : 532
% 0.47/0.65  #    Positive orientable unit clauses  : 117
% 0.47/0.65  #    Positive unorientable unit clauses: 0
% 0.47/0.65  #    Negative unit clauses             : 2
% 0.47/0.65  #    Non-unit-clauses                  : 413
% 0.47/0.65  # Current number of unprocessed clauses: 19558
% 0.47/0.65  # ...number of literals in the above   : 109040
% 0.47/0.65  # Current number of archived formulas  : 0
% 0.47/0.65  # Current number of archived clauses   : 166
% 0.47/0.65  # Clause-clause subsumption calls (NU) : 17245
% 0.47/0.65  # Rec. Clause-clause subsumption calls : 13117
% 0.47/0.65  # Non-unit clause-clause subsumptions  : 1185
% 0.47/0.65  # Unit Clause-clause subsumption calls : 519
% 0.47/0.65  # Rewrite failures with RHS unbound    : 0
% 0.47/0.65  # BW rewrite match attempts            : 1010
% 0.47/0.65  # BW rewrite match successes           : 29
% 0.47/0.65  # Condensation attempts                : 0
% 0.47/0.65  # Condensation successes               : 0
% 0.47/0.65  # Termbank termtop insertions          : 602251
% 0.47/0.65  
% 0.47/0.65  # -------------------------------------------------
% 0.47/0.65  # User time                : 0.298 s
% 0.47/0.65  # System time              : 0.014 s
% 0.47/0.65  # Total time               : 0.312 s
% 0.47/0.65  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
