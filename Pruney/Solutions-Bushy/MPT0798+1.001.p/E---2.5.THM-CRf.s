%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0798+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:12 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   23 (  40 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  103 ( 221 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
          <=> ? [X3] :
                ( v1_relat_1(X3)
                & v1_funct_1(X3)
                & r3_wellord1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(t49_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => r3_wellord1(X2,X1,k2_funct_1(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_wellord1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t50_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(c_0_4,plain,(
    ! [X4,X5,X7] :
      ( ( v1_relat_1(esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( v1_funct_1(esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( r3_wellord1(X4,X5,esk1_2(X4,X5))
        | ~ r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) )
      & ( ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ r3_wellord1(X4,X5,X7)
        | r4_wellord1(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

fof(c_0_5,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ r3_wellord1(X9,X10,X11)
      | r3_wellord1(X10,X9,k2_funct_1(X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_wellord1])])])).

fof(c_0_6,plain,(
    ! [X8] :
      ( ( v1_relat_1(k2_funct_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( v1_funct_1(k2_funct_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_7,plain,
    ( r4_wellord1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r3_wellord1(X2,X1,k2_funct_1(X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r4_wellord1(X1,X2)
             => r4_wellord1(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_wellord1])).

cnf(c_0_12,plain,
    ( r4_wellord1(X1,X2)
    | ~ r3_wellord1(X2,X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])).

cnf(c_0_13,plain,
    ( r3_wellord1(X1,X2,esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( v1_relat_1(esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( v1_funct_1(esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r4_wellord1(esk2_0,esk3_0)
    & ~ r4_wellord1(esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( r4_wellord1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ r4_wellord1(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21]),
    [proof]).

%------------------------------------------------------------------------------
