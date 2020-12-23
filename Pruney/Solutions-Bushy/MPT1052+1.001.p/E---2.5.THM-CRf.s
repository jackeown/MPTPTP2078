%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1052+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   18 (  45 expanded)
%              Number of clauses        :   13 (  21 expanded)
%              Number of leaves         :    2 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 409 expanded)
%              Number of equality atoms :   37 ( 171 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(c_0_2,plain,(
    ! [X6,X7,X8,X9,X11,X12,X13,X14,X15,X17] :
      ( ( v1_relat_1(esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( v1_funct_1(esk1_4(X6,X7,X8,X9))
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( X9 = esk1_4(X6,X7,X8,X9)
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( k1_relat_1(esk1_4(X6,X7,X8,X9)) = X6
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( r1_tarski(k2_relat_1(esk1_4(X6,X7,X8,X9)),X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | X11 != X12
        | k1_relat_1(X12) != X6
        | ~ r1_tarski(k2_relat_1(X12),X7)
        | r2_hidden(X11,X8)
        | X8 != k1_funct_2(X6,X7) )
      & ( ~ r2_hidden(esk2_3(X13,X14,X15),X15)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | esk2_3(X13,X14,X15) != X17
        | k1_relat_1(X17) != X13
        | ~ r1_tarski(k2_relat_1(X17),X14)
        | X15 = k1_funct_2(X13,X14) )
      & ( v1_relat_1(esk3_3(X13,X14,X15))
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( v1_funct_1(esk3_3(X13,X14,X15))
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( esk2_3(X13,X14,X15) = esk3_3(X13,X14,X15)
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( k1_relat_1(esk3_3(X13,X14,X15)) = X13
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) )
      & ( r1_tarski(k2_relat_1(esk3_3(X13,X14,X15)),X14)
        | r2_hidden(esk2_3(X13,X14,X15),X15)
        | X15 = k1_funct_2(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_3,plain,
    ( k1_relat_1(esk1_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_4,plain,
    ( X1 = esk1_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

cnf(c_0_6,plain,
    ( k1_relat_1(X1) = X2
    | X3 != k1_funct_2(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_3,c_0_4])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))
    & ( k1_relat_1(esk6_0) != esk4_0
      | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_relat_1(esk1_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_9,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | X3 != k1_funct_2(X4,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( esk4_0 = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k1_relat_1(esk6_0) != esk4_0
    | ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).

%------------------------------------------------------------------------------
