%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0934+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:26 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   20 (  45 expanded)
%              Number of clauses        :   13 (  15 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 ( 219 expanded)
%              Number of equality atoms :   24 (  87 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_mcart_1,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ( ( k1_mcart_1(X2) = k1_mcart_1(X3)
                  & k2_mcart_1(X2) = k2_mcart_1(X3) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t94_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( ( r2_hidden(X3,X2)
            & r2_hidden(X1,X2)
            & k1_mcart_1(X3) = k1_mcart_1(X1)
            & k2_mcart_1(X3) = k2_mcart_1(X1) )
         => X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_mcart_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,X1)
               => ( ( k1_mcart_1(X2) = k1_mcart_1(X3)
                    & k2_mcart_1(X2) = k2_mcart_1(X3) )
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t95_mcart_1])).

fof(c_0_4,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,X5)
      | v1_xboole_0(X5)
      | r2_hidden(X4,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_5,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v1_relat_1(esk1_0)
    & m1_subset_1(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,esk1_0)
    & k1_mcart_1(esk2_0) = k1_mcart_1(esk3_0)
    & k2_mcart_1(esk2_0) = k2_mcart_1(esk3_0)
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

fof(c_0_6,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ r2_hidden(X8,X7)
      | ~ r2_hidden(X6,X7)
      | k1_mcart_1(X8) != k1_mcart_1(X6)
      | k2_mcart_1(X8) != k2_mcart_1(X6)
      | X8 = X6 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_mcart_1])])])).

cnf(c_0_7,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X2 = X3
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X3,X1)
    | k1_mcart_1(X2) != k1_mcart_1(X3)
    | k2_mcart_1(X2) != k2_mcart_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( X1 = esk3_0
    | k1_mcart_1(X1) != k1_mcart_1(esk3_0)
    | k2_mcart_1(X1) != k2_mcart_1(esk3_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_13]),c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k1_mcart_1(esk2_0) = k1_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,negated_conjecture,
    ( k2_mcart_1(esk2_0) = k2_mcart_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18]),
    [proof]).

%------------------------------------------------------------------------------
