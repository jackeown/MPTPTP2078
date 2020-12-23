%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0889+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:21 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   86 (2241 expanded)
%              Number of clauses        :   59 ( 998 expanded)
%              Number of leaves         :   13 ( 556 expanded)
%              Depth                    :   28
%              Number of atoms          :  254 (6496 expanded)
%              Number of equality atoms :  133 (3326 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(t29_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k3_mcart_1(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
            & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
            & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t49_mcart_1])).

fof(c_0_14,negated_conjecture,
    ( ( r1_tarski(esk2_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))
      | r1_tarski(esk2_0,k3_zfmisc_1(esk3_0,esk4_0,esk2_0))
      | r1_tarski(esk2_0,k3_zfmisc_1(esk4_0,esk2_0,esk3_0)) )
    & esk2_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_15,plain,(
    ! [X6,X7,X8] : k3_zfmisc_1(X6,X7,X8) = k2_zfmisc_1(k2_zfmisc_1(X6,X7),X8) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk2_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(esk3_0,esk4_0,esk2_0))
    | r1_tarski(esk2_0,k3_zfmisc_1(esk4_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tarski(X17,k2_zfmisc_1(X17,X18))
        | X17 = k1_xboole_0 )
      & ( ~ r1_tarski(X17,k2_zfmisc_1(X18,X17))
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | r1_tarski(esk2_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk2_0))
    | r1_tarski(esk2_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18]),c_0_18])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0),esk2_0))
    | r1_tarski(esk2_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0),esk3_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0),esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

fof(c_0_27,plain,(
    ! [X32,X33,X34,X35] :
      ( X32 = k1_xboole_0
      | X33 = k1_xboole_0
      | X34 = k1_xboole_0
      | ~ m1_subset_1(X35,k3_zfmisc_1(X32,X33,X34))
      | X35 = k3_mcart_1(k5_mcart_1(X32,X33,X34,X35),k6_mcart_1(X32,X33,X34,X35),k7_mcart_1(X32,X33,X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0),esk3_0)))
    | m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

fof(c_0_30,plain,(
    ! [X19,X21,X22,X23] :
      ( ( r2_hidden(esk1_1(X19),X19)
        | X19 = k1_xboole_0 )
      & ( ~ r2_hidden(X21,X19)
        | esk1_1(X19) != k3_mcart_1(X21,X22,X23)
        | X19 = k1_xboole_0 )
      & ( ~ r2_hidden(X22,X19)
        | esk1_1(X19) != k3_mcart_1(X21,X22,X23)
        | X19 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_mcart_1])])])])])])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)))
    | m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0),esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk1_1(esk2_0),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0),esk3_0))
    | m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_24])).

fof(c_0_36,plain,(
    ! [X13,X14,X15,X16] :
      ( ~ m1_subset_1(X16,k3_zfmisc_1(X13,X14,X15))
      | m1_subset_1(k6_mcart_1(X13,X14,X15,X16),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_37,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k7_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24])).

cnf(c_0_38,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k7_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_40,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k7_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | m1_subset_1(esk1_1(esk2_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)))
    | m1_subset_1(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_43,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk1_1(X2) != k3_mcart_1(X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k7_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | k3_mcart_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k6_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k7_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_41]),c_0_24])).

fof(c_0_45,plain,(
    ! [X39] :
      ( ~ v1_xboole_0(X39)
      | X39 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_46,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,X25)
      | v1_xboole_0(X25)
      | r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0)
    | m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k6_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k7_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | esk1_1(X1) != esk1_1(esk2_0)
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk1_1(esk2_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_33]),c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k6_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k7_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_24])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k6_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k7_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_51]),c_0_24])).

cnf(c_0_55,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk1_1(X2) != k3_mcart_1(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_56,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k6_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),k7_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_24]),c_0_54])).

fof(c_0_57,plain,(
    ! [X9,X10,X11,X12] :
      ( ~ m1_subset_1(X12,k3_zfmisc_1(X9,X10,X11))
      | m1_subset_1(k5_mcart_1(X9,X10,X11,X12),X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

cnf(c_0_58,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | esk1_1(X1) != esk1_1(esk2_0)
    | ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_60,plain,(
    ! [X26,X27,X28] :
      ( ( X26 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 = k1_xboole_0
        | k3_zfmisc_1(X26,X27,X28) != k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | k3_zfmisc_1(X26,X27,X28) = k1_xboole_0 )
      & ( X27 != k1_xboole_0
        | k3_zfmisc_1(X26,X27,X28) = k1_xboole_0 )
      & ( X28 != k1_xboole_0
        | k3_zfmisc_1(X26,X27,X28) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ r2_hidden(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_58]),c_0_24])).

cnf(c_0_62,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_18])).

cnf(c_0_63,plain,
    ( k3_zfmisc_1(X2,X1,X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_53]),c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k7_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | m1_subset_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_41])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X2,X1),X3) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_63,c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),k7_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0))) = esk1_1(esk2_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0),X2) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | esk1_1(X1) != esk1_1(esk2_0)
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_67])).

cnf(c_0_71,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_18])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ r2_hidden(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_24])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_69]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_53]),c_0_24])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk4_0,esk2_0,esk3_0,esk1_1(esk2_0)),esk2_0)
    | m1_subset_1(k5_mcart_1(esk2_0,esk3_0,esk4_0,esk1_1(esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_51])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_74])).

fof(c_0_78,plain,(
    ! [X31] :
      ( ~ r1_tarski(X31,k1_xboole_0)
      | X31 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_79,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_64])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_77])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_79]),c_0_80]),c_0_80]),c_0_72]),c_0_72]),c_0_72])])).

cnf(c_0_83,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_83]),c_0_80]),c_0_72]),c_0_83]),c_0_72]),c_0_72]),c_0_83]),c_0_80])])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_84]),c_0_24]),
    [proof]).

%------------------------------------------------------------------------------
