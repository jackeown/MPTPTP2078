%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t63_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:26 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  90 expanded)
%              Number of clauses        :   20 (  29 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  146 ( 549 expanded)
%              Number of equality atoms :   50 ( 194 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',t63_funct_1)).

fof(l72_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_relat_1(X4)
                & v1_funct_1(X4) )
             => ( ( k2_relat_1(X2) = X1
                  & k5_relat_1(X2,X3) = k6_relat_1(k1_relat_1(X4))
                  & k5_relat_1(X3,X4) = k6_relat_1(X1) )
               => X4 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',l72_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',t61_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t63_funct_1.p',t55_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & k2_relat_1(X1) = k1_relat_1(X2)
                & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
             => X2 = k2_funct_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_funct_1])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | k2_relat_1(X12) != X11
      | k5_relat_1(X12,X13) != k6_relat_1(k1_relat_1(X14))
      | k5_relat_1(X13,X14) != k6_relat_1(X11)
      | X14 = X12 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l72_funct_1])])])).

fof(c_0_7,plain,(
    ! [X16] :
      ( ( k5_relat_1(X16,k2_funct_1(X16)) = k6_relat_1(k1_relat_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k5_relat_1(k2_funct_1(X16),X16) = k6_relat_1(k2_relat_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk1_0)
    & k2_relat_1(esk1_0) = k1_relat_1(esk2_0)
    & k5_relat_1(esk1_0,esk2_0) = k6_relat_1(k1_relat_1(esk1_0))
    & esk2_0 != k2_funct_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( X3 = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | k2_relat_1(X1) != X4
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X3))
    | k5_relat_1(X2,X3) != k6_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( X1 = X2
    | k5_relat_1(X1,X3) != k6_relat_1(k1_relat_1(X2))
    | k5_relat_1(X3,X2) != k6_relat_1(k2_relat_1(X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk1_0),esk1_0) = k6_relat_1(k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14])])).

fof(c_0_17,plain,(
    ! [X7] :
      ( ( v1_relat_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( v1_funct_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_18,negated_conjecture,
    ( k2_funct_1(esk1_0) = X1
    | k5_relat_1(esk1_0,X1) != k6_relat_1(k2_relat_1(k2_funct_1(esk1_0)))
    | k6_relat_1(k1_relat_1(esk2_0)) != k6_relat_1(k1_relat_1(X1))
    | ~ v1_funct_1(k2_funct_1(esk1_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_13]),c_0_14])])).

cnf(c_0_19,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( k2_funct_1(esk1_0) = X1
    | k5_relat_1(esk1_0,X1) != k6_relat_1(k2_relat_1(k2_funct_1(esk1_0)))
    | k6_relat_1(k1_relat_1(esk2_0)) != k6_relat_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13]),c_0_14])])).

cnf(c_0_21,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X15] :
      ( ( k2_relat_1(X15) = k1_relat_1(k2_funct_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k1_relat_1(X15) = k2_relat_1(k2_funct_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_23,negated_conjecture,
    ( k2_funct_1(esk1_0) = X1
    | k5_relat_1(esk1_0,X1) != k6_relat_1(k2_relat_1(k2_funct_1(esk1_0)))
    | k6_relat_1(k1_relat_1(esk2_0)) != k6_relat_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_13]),c_0_14])])).

cnf(c_0_24,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( k5_relat_1(esk1_0,esk2_0) = k6_relat_1(k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( k2_funct_1(esk1_0) = X1
    | k5_relat_1(esk1_0,X1) != k5_relat_1(esk1_0,esk2_0)
    | k6_relat_1(k1_relat_1(esk2_0)) != k6_relat_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 != k2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27]),c_0_28])]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
