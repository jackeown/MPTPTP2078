%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0932+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:26 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  45 expanded)
%              Number of clauses        :   12 (  17 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 126 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t93_mcart_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k2_mcart_1(X2),k11_relat_1(X1,k1_mcart_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_mcart_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t92_mcart_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ! [X2] : k11_relat_1(X1,X2) = a_2_0_mcart_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_mcart_1)).

fof(fraenkel_a_2_0_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,a_2_0_mcart_1(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,X2)
            & X1 = k2_mcart_1(X4)
            & k1_mcart_1(X4) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r2_hidden(k2_mcart_1(X2),k11_relat_1(X1,k1_mcart_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t93_mcart_1])).

fof(c_0_6,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & r2_hidden(esk3_0,esk2_0)
    & ~ r2_hidden(k2_mcart_1(esk3_0),k11_relat_1(esk2_0,k1_mcart_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ v1_relat_1(X15)
      | k11_relat_1(X15,X16) = a_2_0_mcart_1(X15,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t92_mcart_1])])])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X9,X10] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),X6)
        | ~ r2_hidden(X5,a_2_0_mcart_1(X6,X7))
        | v1_xboole_0(X6)
        | ~ v1_relat_1(X6) )
      & ( X5 = k2_mcart_1(esk1_3(X5,X6,X7))
        | ~ r2_hidden(X5,a_2_0_mcart_1(X6,X7))
        | v1_xboole_0(X6)
        | ~ v1_relat_1(X6) )
      & ( k1_mcart_1(esk1_3(X5,X6,X7)) = X7
        | ~ r2_hidden(X5,a_2_0_mcart_1(X6,X7))
        | v1_xboole_0(X6)
        | ~ v1_relat_1(X6) )
      & ( ~ m1_subset_1(X10,X6)
        | X5 != k2_mcart_1(X10)
        | k1_mcart_1(X10) != X9
        | r2_hidden(X5,a_2_0_mcart_1(X6,X9))
        | v1_xboole_0(X6)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_mcart_1])])])])])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(esk3_0),k11_relat_1(esk2_0,k1_mcart_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X1)
    | k11_relat_1(X1,X2) = a_2_0_mcart_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,a_2_0_mcart_1(X2,X4))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X3 != k2_mcart_1(X1)
    | k1_mcart_1(X1) != X4
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(esk3_0),a_2_0_mcart_1(esk2_0,k1_mcart_1(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_18,plain,
    ( r2_hidden(k2_mcart_1(X1),a_2_0_mcart_1(X2,k1_mcart_1(X1)))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

fof(c_0_19,plain,(
    ! [X11,X12] :
      ( ~ r2_hidden(X11,X12)
      | m1_subset_1(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14])]),c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_10])]),
    [proof]).

%------------------------------------------------------------------------------
