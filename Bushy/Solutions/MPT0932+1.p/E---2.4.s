%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : mcart_1__t93_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:16 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   23 (  33 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   74 ( 102 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fraenkel_a_2_0_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,a_2_0_mcart_1(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,X2)
            & X1 = k2_mcart_1(X4)
            & k1_mcart_1(X4) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',fraenkel_a_2_0_mcart_1)).

fof(t93_mcart_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k2_mcart_1(X2),k11_relat_1(X1,k1_mcart_1(X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t93_mcart_1)).

fof(t92_mcart_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ! [X2] : k11_relat_1(X1,X2) = a_2_0_mcart_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t92_mcart_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t7_boole)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t93_mcart_1.p',t1_subset)).

fof(c_0_5,plain,(
    ! [X13,X14,X15,X17,X18] :
      ( ( m1_subset_1(esk4_3(X13,X14,X15),X14)
        | ~ r2_hidden(X13,a_2_0_mcart_1(X14,X15))
        | v1_xboole_0(X14)
        | ~ v1_relat_1(X14) )
      & ( X13 = k2_mcart_1(esk4_3(X13,X14,X15))
        | ~ r2_hidden(X13,a_2_0_mcart_1(X14,X15))
        | v1_xboole_0(X14)
        | ~ v1_relat_1(X14) )
      & ( k1_mcart_1(esk4_3(X13,X14,X15)) = X15
        | ~ r2_hidden(X13,a_2_0_mcart_1(X14,X15))
        | v1_xboole_0(X14)
        | ~ v1_relat_1(X14) )
      & ( ~ m1_subset_1(X18,X14)
        | X13 != k2_mcart_1(X18)
        | k1_mcart_1(X18) != X17
        | r2_hidden(X13,a_2_0_mcart_1(X14,X17))
        | v1_xboole_0(X14)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_mcart_1])])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r2_hidden(k2_mcart_1(X2),k11_relat_1(X1,k1_mcart_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t93_mcart_1])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,a_2_0_mcart_1(X2,X4))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X3 != k2_mcart_1(X1)
    | k1_mcart_1(X1) != X4
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X37,X38] :
      ( v1_xboole_0(X37)
      | ~ v1_relat_1(X37)
      | k11_relat_1(X37,X38) = a_2_0_mcart_1(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t92_mcart_1])])])])).

fof(c_0_9,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | ~ v1_xboole_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & r2_hidden(esk2_0,esk1_0)
    & ~ r2_hidden(k2_mcart_1(esk2_0),k11_relat_1(esk1_0,k1_mcart_1(esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k2_mcart_1(X2),a_2_0_mcart_1(X1,k1_mcart_1(X2)))
    | ~ m1_subset_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).

cnf(c_0_12,plain,
    ( v1_xboole_0(X1)
    | k11_relat_1(X1,X2) = a_2_0_mcart_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ r2_hidden(k2_mcart_1(esk2_0),k11_relat_1(esk1_0,k1_mcart_1(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(k2_mcart_1(X2),k11_relat_1(X1,k1_mcart_1(X2)))
    | ~ m1_subset_1(X2,X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_20,negated_conjecture,
    ( ~ m1_subset_1(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14])]),
    [proof]).
%------------------------------------------------------------------------------
