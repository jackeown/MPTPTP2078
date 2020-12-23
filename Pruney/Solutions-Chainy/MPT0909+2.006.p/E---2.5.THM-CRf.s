%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:09 EST 2020

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 243 expanded)
%              Number of clauses        :   48 ( 101 expanded)
%              Number of leaves         :   12 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  249 (1187 expanded)
%              Number of equality atoms :  135 ( 682 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X6 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X6 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k5_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_mcart_1])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(k1_mcart_1(X27),X28)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) )
      & ( r2_hidden(k2_mcart_1(X27),X29)
        | ~ r2_hidden(X27,k2_zfmisc_1(X28,X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_15,negated_conjecture,(
    ! [X46,X47,X48] :
      ( m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))
      & ( ~ m1_subset_1(X46,esk2_0)
        | ~ m1_subset_1(X47,esk3_0)
        | ~ m1_subset_1(X48,esk4_0)
        | esk6_0 != k3_mcart_1(X46,X47,X48)
        | esk5_0 = X46 )
      & esk2_0 != k1_xboole_0
      & esk3_0 != k1_xboole_0
      & esk4_0 != k1_xboole_0
      & esk5_0 != k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] : k3_zfmisc_1(X20,X21,X22) = k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X33,X34,X35,X36] :
      ( X33 = k1_xboole_0
      | X34 = k1_xboole_0
      | X35 = k1_xboole_0
      | ~ m1_subset_1(X36,k3_zfmisc_1(X33,X34,X35))
      | X36 = k3_mcart_1(k5_mcart_1(X33,X34,X35,X36),k6_mcart_1(X33,X34,X35,X36),k7_mcart_1(X33,X34,X35,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] : k3_mcart_1(X17,X18,X19) = k4_tarski(k4_tarski(X17,X18),X19) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_19,plain,(
    ! [X37,X38,X39,X40] :
      ( ( k5_mcart_1(X37,X38,X39,X40) = k1_mcart_1(k1_mcart_1(X40))
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k6_mcart_1(X37,X38,X39,X40) = k2_mcart_1(k1_mcart_1(X40))
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( k7_mcart_1(X37,X38,X39,X40) = k2_mcart_1(X40)
        | ~ m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))
        | X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | X13 = X14
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_21,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X30,X31,X32] :
      ( ( X30 = k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0
        | k3_zfmisc_1(X30,X31,X32) != k1_xboole_0 )
      & ( X30 != k1_xboole_0
        | k3_zfmisc_1(X30,X31,X32) = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k3_zfmisc_1(X30,X31,X32) = k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k3_zfmisc_1(X30,X31,X32) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_31,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_24])).

cnf(c_0_34,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_35,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_36,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))
      | m1_subset_1(k7_mcart_1(X23,X24,X25,X26),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k2_mcart_1(X4)) = X4
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_24])).

cnf(c_0_42,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_45,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k2_mcart_1(k1_mcart_1(X4))),k2_mcart_1(X4)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_52,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 = X1
    | ~ m1_subset_1(X1,esk2_0)
    | ~ m1_subset_1(X2,esk3_0)
    | ~ m1_subset_1(X3,esk4_0)
    | esk6_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_58,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X1)),k2_mcart_1(k1_mcart_1(X1))),k2_mcart_1(X1)) = X1
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 = X1
    | esk6_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk3_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0))),k2_mcart_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_32]),c_0_49]),c_0_48]),c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_32]),c_0_49]),c_0_48]),c_0_47])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 != k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = k1_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0) != k1_mcart_1(k1_mcart_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_51]),c_0_32])]),c_0_47]),c_0_48]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.86/1.04  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.86/1.04  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.86/1.04  #
% 0.86/1.04  # Preprocessing time       : 0.027 s
% 0.86/1.04  # Presaturation interreduction done
% 0.86/1.04  
% 0.86/1.04  # Proof found!
% 0.86/1.04  # SZS status Theorem
% 0.86/1.04  # SZS output start CNFRefutation
% 0.86/1.04  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.86/1.04  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.86/1.04  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.86/1.04  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.86/1.04  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.86/1.04  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.86/1.04  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.86/1.04  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.86/1.04  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.86/1.04  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.86/1.04  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.86/1.04  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.86/1.04  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.86/1.04  fof(c_0_13, plain, ![X27, X28, X29]:((r2_hidden(k1_mcart_1(X27),X28)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))&(r2_hidden(k2_mcart_1(X27),X29)|~r2_hidden(X27,k2_zfmisc_1(X28,X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.86/1.04  fof(c_0_14, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.86/1.04  fof(c_0_15, negated_conjecture, ![X46, X47, X48]:(m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))&((~m1_subset_1(X46,esk2_0)|(~m1_subset_1(X47,esk3_0)|(~m1_subset_1(X48,esk4_0)|(esk6_0!=k3_mcart_1(X46,X47,X48)|esk5_0=X46))))&(((esk2_0!=k1_xboole_0&esk3_0!=k1_xboole_0)&esk4_0!=k1_xboole_0)&esk5_0!=k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.86/1.04  fof(c_0_16, plain, ![X20, X21, X22]:k3_zfmisc_1(X20,X21,X22)=k2_zfmisc_1(k2_zfmisc_1(X20,X21),X22), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.86/1.04  fof(c_0_17, plain, ![X33, X34, X35, X36]:(X33=k1_xboole_0|X34=k1_xboole_0|X35=k1_xboole_0|(~m1_subset_1(X36,k3_zfmisc_1(X33,X34,X35))|X36=k3_mcart_1(k5_mcart_1(X33,X34,X35,X36),k6_mcart_1(X33,X34,X35,X36),k7_mcart_1(X33,X34,X35,X36)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.86/1.04  fof(c_0_18, plain, ![X17, X18, X19]:k3_mcart_1(X17,X18,X19)=k4_tarski(k4_tarski(X17,X18),X19), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.86/1.04  fof(c_0_19, plain, ![X37, X38, X39, X40]:(((k5_mcart_1(X37,X38,X39,X40)=k1_mcart_1(k1_mcart_1(X40))|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))&(k6_mcart_1(X37,X38,X39,X40)=k2_mcart_1(k1_mcart_1(X40))|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0)))&(k7_mcart_1(X37,X38,X39,X40)=k2_mcart_1(X40)|~m1_subset_1(X40,k3_zfmisc_1(X37,X38,X39))|(X37=k1_xboole_0|X38=k1_xboole_0|X39=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.86/1.04  fof(c_0_20, plain, ![X13, X14]:(~v1_xboole_0(X13)|X13=X14|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.86/1.04  cnf(c_0_21, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.86/1.04  cnf(c_0_22, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.86/1.04  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,k3_zfmisc_1(esk2_0,esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.86/1.04  cnf(c_0_24, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.86/1.04  cnf(c_0_25, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.86/1.04  cnf(c_0_26, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.86/1.04  cnf(c_0_27, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.86/1.04  fof(c_0_28, plain, ![X30, X31, X32]:((X30=k1_xboole_0|X31=k1_xboole_0|X32=k1_xboole_0|k3_zfmisc_1(X30,X31,X32)!=k1_xboole_0)&(((X30!=k1_xboole_0|k3_zfmisc_1(X30,X31,X32)=k1_xboole_0)&(X31!=k1_xboole_0|k3_zfmisc_1(X30,X31,X32)=k1_xboole_0))&(X32!=k1_xboole_0|k3_zfmisc_1(X30,X31,X32)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.86/1.04  cnf(c_0_29, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.86/1.04  cnf(c_0_30, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.86/1.04  cnf(c_0_31, plain, (r2_hidden(k1_mcart_1(X1),X2)|v1_xboole_0(k2_zfmisc_1(X2,X3))|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.86/1.04  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk6_0,k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.86/1.04  cnf(c_0_33, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_24])).
% 0.86/1.04  cnf(c_0_34, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_27, c_0_24])).
% 0.86/1.04  cnf(c_0_35, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.86/1.04  fof(c_0_36, plain, ![X23, X24, X25, X26]:(~m1_subset_1(X26,k3_zfmisc_1(X23,X24,X25))|m1_subset_1(k7_mcart_1(X23,X24,X25,X26),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.86/1.04  cnf(c_0_37, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.86/1.04  cnf(c_0_38, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.86/1.04  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.86/1.04  cnf(c_0_40, plain, (k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k2_mcart_1(X4))=X4|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.86/1.04  cnf(c_0_41, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_35, c_0_24])).
% 0.86/1.04  cnf(c_0_42, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.86/1.04  cnf(c_0_43, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.86/1.04  fof(c_0_44, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.86/1.04  cnf(c_0_45, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_24])).
% 0.86/1.04  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.86/1.04  cnf(c_0_47, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.86/1.04  cnf(c_0_48, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.86/1.04  cnf(c_0_49, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.86/1.04  cnf(c_0_50, plain, (k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k2_mcart_1(k1_mcart_1(X4))),k2_mcart_1(X4))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.86/1.04  cnf(c_0_51, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_42, c_0_24])).
% 0.86/1.04  cnf(c_0_52, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_43, c_0_24])).
% 0.86/1.04  cnf(c_0_53, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.86/1.04  cnf(c_0_54, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.86/1.04  cnf(c_0_55, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.86/1.04  cnf(c_0_56, negated_conjecture, (r2_hidden(k1_mcart_1(esk6_0),k2_zfmisc_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48]), c_0_49])).
% 0.86/1.04  cnf(c_0_57, negated_conjecture, (esk5_0=X1|~m1_subset_1(X1,esk2_0)|~m1_subset_1(X2,esk3_0)|~m1_subset_1(X3,esk4_0)|esk6_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.86/1.04  cnf(c_0_58, plain, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X1)),k2_mcart_1(k1_mcart_1(X1))),k2_mcart_1(X1))=X1|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.86/1.04  cnf(c_0_59, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|m1_subset_1(k2_mcart_1(X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_52, c_0_34])).
% 0.86/1.04  cnf(c_0_60, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_53, c_0_54])).
% 0.86/1.04  cnf(c_0_61, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.86/1.04  cnf(c_0_62, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0)), inference(spm,[status(thm)],[c_0_21, c_0_56])).
% 0.86/1.04  cnf(c_0_63, negated_conjecture, (esk5_0=X1|esk6_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk3_0)|~m1_subset_1(X1,esk2_0)), inference(rw,[status(thm)],[c_0_57, c_0_26])).
% 0.86/1.04  cnf(c_0_64, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk6_0)),k2_mcart_1(k1_mcart_1(esk6_0))),k2_mcart_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_32]), c_0_49]), c_0_48]), c_0_47])).
% 0.86/1.04  cnf(c_0_65, negated_conjecture, (m1_subset_1(k2_mcart_1(esk6_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_32]), c_0_49]), c_0_48]), c_0_47])).
% 0.86/1.04  cnf(c_0_66, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk6_0)),esk3_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.86/1.04  cnf(c_0_67, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk6_0)),esk2_0)), inference(spm,[status(thm)],[c_0_60, c_0_62])).
% 0.86/1.04  cnf(c_0_68, negated_conjecture, (esk5_0!=k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.86/1.04  cnf(c_0_69, negated_conjecture, (esk5_0=k1_mcart_1(k1_mcart_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66]), c_0_67])])).
% 0.86/1.04  cnf(c_0_70, negated_conjecture, (k5_mcart_1(esk2_0,esk3_0,esk4_0,esk6_0)!=k1_mcart_1(k1_mcart_1(esk6_0))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.86/1.04  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_51]), c_0_32])]), c_0_47]), c_0_48]), c_0_49]), ['proof']).
% 0.86/1.04  # SZS output end CNFRefutation
% 0.86/1.04  # Proof object total steps             : 72
% 0.86/1.04  # Proof object clause steps            : 48
% 0.86/1.04  # Proof object formula steps           : 24
% 0.86/1.04  # Proof object conjectures             : 23
% 0.86/1.04  # Proof object clause conjectures      : 20
% 0.86/1.04  # Proof object formula conjectures     : 3
% 0.86/1.04  # Proof object initial clauses used    : 21
% 0.86/1.04  # Proof object initial formulas used   : 12
% 0.86/1.04  # Proof object generating inferences   : 17
% 0.86/1.04  # Proof object simplifying inferences  : 29
% 0.86/1.04  # Training examples: 0 positive, 0 negative
% 0.86/1.04  # Parsed axioms                        : 12
% 0.86/1.04  # Removed by relevancy pruning/SinE    : 0
% 0.86/1.04  # Initial clauses                      : 27
% 0.86/1.04  # Removed in clause preprocessing      : 2
% 0.86/1.04  # Initial clauses in saturation        : 25
% 0.86/1.04  # Processed clauses                    : 7632
% 0.86/1.04  # ...of these trivial                  : 10
% 0.86/1.04  # ...subsumed                          : 7237
% 0.86/1.04  # ...remaining for further processing  : 385
% 0.86/1.04  # Other redundant clauses eliminated   : 8
% 0.86/1.04  # Clauses deleted for lack of memory   : 0
% 0.86/1.04  # Backward-subsumed                    : 56
% 0.86/1.04  # Backward-rewritten                   : 23
% 0.86/1.04  # Generated clauses                    : 63998
% 0.86/1.04  # ...of the previous two non-trivial   : 60098
% 0.86/1.04  # Contextual simplify-reflections      : 17
% 0.86/1.04  # Paramodulations                      : 63969
% 0.86/1.04  # Factorizations                       : 15
% 0.86/1.04  # Equation resolutions                 : 14
% 0.86/1.04  # Propositional unsat checks           : 0
% 0.86/1.04  #    Propositional check models        : 0
% 0.86/1.04  #    Propositional check unsatisfiable : 0
% 0.86/1.04  #    Propositional clauses             : 0
% 0.86/1.04  #    Propositional clauses after purity: 0
% 0.86/1.04  #    Propositional unsat core size     : 0
% 0.86/1.04  #    Propositional preprocessing time  : 0.000
% 0.86/1.04  #    Propositional encoding time       : 0.000
% 0.86/1.04  #    Propositional solver time         : 0.000
% 0.86/1.04  #    Success case prop preproc time    : 0.000
% 0.86/1.04  #    Success case prop encoding time   : 0.000
% 0.86/1.04  #    Success case prop solver time     : 0.000
% 0.86/1.04  # Current number of processed clauses  : 281
% 0.86/1.04  #    Positive orientable unit clauses  : 14
% 0.86/1.04  #    Positive unorientable unit clauses: 0
% 0.86/1.04  #    Negative unit clauses             : 8
% 0.86/1.04  #    Non-unit-clauses                  : 259
% 0.86/1.04  # Current number of unprocessed clauses: 52029
% 0.86/1.04  # ...number of literals in the above   : 259513
% 0.86/1.04  # Current number of archived formulas  : 0
% 0.86/1.04  # Current number of archived clauses   : 106
% 0.86/1.04  # Clause-clause subsumption calls (NU) : 93547
% 0.86/1.04  # Rec. Clause-clause subsumption calls : 68017
% 0.86/1.04  # Non-unit clause-clause subsumptions  : 6626
% 0.86/1.04  # Unit Clause-clause subsumption calls : 189
% 0.86/1.04  # Rewrite failures with RHS unbound    : 0
% 0.86/1.04  # BW rewrite match attempts            : 5
% 0.86/1.04  # BW rewrite match successes           : 5
% 0.86/1.04  # Condensation attempts                : 0
% 0.86/1.04  # Condensation successes               : 0
% 0.86/1.04  # Termbank termtop insertions          : 788794
% 0.86/1.05  
% 0.86/1.05  # -------------------------------------------------
% 0.86/1.05  # User time                : 0.675 s
% 0.86/1.05  # System time              : 0.024 s
% 0.86/1.05  # Total time               : 0.699 s
% 0.86/1.05  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
