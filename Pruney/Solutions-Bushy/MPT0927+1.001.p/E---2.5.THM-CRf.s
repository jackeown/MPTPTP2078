%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0927+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:25 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 636 expanded)
%              Number of clauses        :   75 ( 301 expanded)
%              Number of leaves         :   15 ( 177 expanded)
%              Depth                    :   27
%              Number of atoms          :  498 (2735 expanded)
%              Number of equality atoms :  286 ( 994 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t87_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(X1))
     => ! [X6] :
          ( m1_subset_1(X6,k1_zfmisc_1(X2))
         => ! [X7] :
              ( m1_subset_1(X7,k1_zfmisc_1(X3))
             => ! [X8] :
                  ( m1_subset_1(X8,k1_zfmisc_1(X4))
                 => ! [X9] :
                      ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
                     => ( r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))
                       => ( r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)
                          & r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6)
                          & r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7)
                          & r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

fof(t86_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0
        & X5 != k1_xboole_0
        & X6 != k1_xboole_0
        & X7 != k1_xboole_0
        & X8 != k1_xboole_0
        & ? [X9] :
            ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
            & ? [X10] :
                ( m1_subset_1(X10,k4_zfmisc_1(X5,X6,X7,X8))
                & X9 = X10
                & ~ ( k8_mcart_1(X1,X2,X3,X4,X9) = k8_mcart_1(X5,X6,X7,X8,X10)
                    & k9_mcart_1(X1,X2,X3,X4,X9) = k9_mcart_1(X5,X6,X7,X8,X10)
                    & k10_mcart_1(X1,X2,X3,X4,X9) = k10_mcart_1(X5,X6,X7,X8,X10)
                    & k11_mcart_1(X1,X2,X3,X4,X9) = k11_mcart_1(X5,X6,X7,X8,X10) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(dt_k8_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X5),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k9_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X5),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(dt_k11_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X5),X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

fof(dt_k10_mcart_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4))
     => m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X5),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k1_zfmisc_1(X1))
       => ! [X6] :
            ( m1_subset_1(X6,k1_zfmisc_1(X2))
           => ! [X7] :
                ( m1_subset_1(X7,k1_zfmisc_1(X3))
               => ! [X8] :
                    ( m1_subset_1(X8,k1_zfmisc_1(X4))
                   => ! [X9] :
                        ( m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4))
                       => ( r2_hidden(X9,k4_zfmisc_1(X5,X6,X7,X8))
                         => ( r2_hidden(k8_mcart_1(X1,X2,X3,X4,X9),X5)
                            & r2_hidden(k9_mcart_1(X1,X2,X3,X4,X9),X6)
                            & r2_hidden(k10_mcart_1(X1,X2,X3,X4,X9),X7)
                            & r2_hidden(k11_mcart_1(X1,X2,X3,X4,X9),X8) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t87_mcart_1])).

fof(c_0_16,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54,X55,X56] :
      ( ( k8_mcart_1(X47,X48,X49,X50,X55) = k8_mcart_1(X51,X52,X53,X54,X56)
        | ~ m1_subset_1(X56,k4_zfmisc_1(X51,X52,X53,X54))
        | X55 != X56
        | ~ m1_subset_1(X55,k4_zfmisc_1(X47,X48,X49,X50))
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 )
      & ( k9_mcart_1(X47,X48,X49,X50,X55) = k9_mcart_1(X51,X52,X53,X54,X56)
        | ~ m1_subset_1(X56,k4_zfmisc_1(X51,X52,X53,X54))
        | X55 != X56
        | ~ m1_subset_1(X55,k4_zfmisc_1(X47,X48,X49,X50))
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 )
      & ( k10_mcart_1(X47,X48,X49,X50,X55) = k10_mcart_1(X51,X52,X53,X54,X56)
        | ~ m1_subset_1(X56,k4_zfmisc_1(X51,X52,X53,X54))
        | X55 != X56
        | ~ m1_subset_1(X55,k4_zfmisc_1(X47,X48,X49,X50))
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 )
      & ( k11_mcart_1(X47,X48,X49,X50,X55) = k11_mcart_1(X51,X52,X53,X54,X56)
        | ~ m1_subset_1(X56,k4_zfmisc_1(X51,X52,X53,X54))
        | X55 != X56
        | ~ m1_subset_1(X55,k4_zfmisc_1(X47,X48,X49,X50))
        | X47 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 = k1_xboole_0
        | X50 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_mcart_1])])])])).

fof(c_0_17,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | ~ v1_xboole_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(esk5_0))
    & m1_subset_1(esk10_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0))
    & r2_hidden(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0))
    & ( ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
      | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)
      | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
      | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ~ m1_subset_1(X25,k4_zfmisc_1(X21,X22,X23,X24))
      | m1_subset_1(k8_mcart_1(X21,X22,X23,X24,X25),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_mcart_1])])).

cnf(c_0_20,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k8_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | m1_subset_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X37,X38,X39,X40] :
      ( ( X37 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 = k1_xboole_0
        | k4_zfmisc_1(X37,X38,X39,X40) != k1_xboole_0 )
      & ( X37 != k1_xboole_0
        | k4_zfmisc_1(X37,X38,X39,X40) = k1_xboole_0 )
      & ( X38 != k1_xboole_0
        | k4_zfmisc_1(X37,X38,X39,X40) = k1_xboole_0 )
      & ( X39 != k1_xboole_0
        | k4_zfmisc_1(X37,X38,X39,X40) = k1_xboole_0 )
      & ( X40 != k1_xboole_0
        | k4_zfmisc_1(X37,X38,X39,X40) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_25,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_26,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_27,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k9_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_28,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X35,X36)
      | v1_xboole_0(X36)
      | r2_hidden(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_29,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( ~ m1_subset_1(X30,k4_zfmisc_1(X26,X27,X28,X29))
      | m1_subset_1(k9_mcart_1(X26,X27,X28,X29,X30),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_mcart_1])])).

cnf(c_0_30,plain,
    ( m1_subset_1(k8_mcart_1(X2,X3,X4,X5,X1),X2)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( k8_mcart_1(X1,X2,X3,X4,X5) = k8_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( k4_zfmisc_1(X2,X1,X3,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_39,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ~ m1_subset_1(X20,k4_zfmisc_1(X16,X17,X18,X19))
      | m1_subset_1(k11_mcart_1(X16,X17,X18,X19,X20),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_mcart_1])])).

cnf(c_0_40,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k11_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ r2_hidden(k9_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk7_0)
    | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
    | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( k9_mcart_1(X1,X2,X3,X4,X5) = k9_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk2_0,esk3_0,esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( m1_subset_1(k9_mcart_1(X2,X3,X4,X5,X1),X3)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X9),X5)
    | ~ m1_subset_1(X9,k4_zfmisc_1(X5,X6,X7,X8))
    | ~ m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk10_0,k4_zfmisc_1(esk6_0,esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_49,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_36]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_35])])).

cnf(c_0_51,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_38]),c_0_35])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k11_mcart_1(X2,X3,X4,X5,X1),X5)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,plain,
    ( k11_mcart_1(X1,X2,X3,X4,X5) = k11_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_40])).

fof(c_0_54,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ~ m1_subset_1(X15,k4_zfmisc_1(X11,X12,X13,X14))
      | m1_subset_1(k10_mcart_1(X11,X12,X13,X14,X15),X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_mcart_1])])).

cnf(c_0_55,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k10_mcart_1(X6,X7,X8,X9,X10)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | X9 = k1_xboole_0
    | ~ m1_subset_1(X10,k4_zfmisc_1(X6,X7,X8,X9))
    | X5 != X10
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
    | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)
    | ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ r2_hidden(k9_mcart_1(X1,X2,X3,X4,esk10_0),esk7_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_57,plain,
    ( r2_hidden(k9_mcart_1(X1,X2,X3,X4,X5),X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | m1_subset_1(k8_mcart_1(X4,X3,X2,X1,esk10_0),esk6_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X4,X3,X2,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X9),X8)
    | ~ m1_subset_1(X9,k4_zfmisc_1(X5,X6,X7,X8))
    | ~ m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( m1_subset_1(k10_mcart_1(X2,X3,X4,X5,X1),X4)
    | ~ m1_subset_1(X1,k4_zfmisc_1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,plain,
    ( k10_mcart_1(X1,X2,X3,X4,X5) = k10_mcart_1(X6,X7,X8,X9,X5)
    | X9 = k1_xboole_0
    | X8 = k1_xboole_0
    | X7 = k1_xboole_0
    | X6 = k1_xboole_0
    | X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X5,k4_zfmisc_1(X6,X7,X8,X9))
    | ~ m1_subset_1(X5,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | v1_xboole_0(esk7_0)
    | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
    | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)
    | ~ r2_hidden(k8_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk6_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X3,esk7_0,X2,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | r2_hidden(k8_mcart_1(X1,X2,X3,X4,esk10_0),esk6_0)
    | v1_xboole_0(esk6_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | m1_subset_1(k11_mcart_1(X4,X3,X2,X1,esk10_0),esk9_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X4,X3,X2,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | X5 = k1_xboole_0
    | X6 = k1_xboole_0
    | X7 = k1_xboole_0
    | X8 = k1_xboole_0
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X9),X7)
    | ~ m1_subset_1(X9,k4_zfmisc_1(X5,X6,X7,X8))
    | ~ m1_subset_1(X9,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | v1_xboole_0(esk6_0)
    | v1_xboole_0(esk7_0)
    | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
    | ~ r2_hidden(k11_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk9_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,esk7_0,X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_43])])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | r2_hidden(k11_mcart_1(X1,X2,X3,X4,esk10_0),esk9_0)
    | v1_xboole_0(esk9_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | m1_subset_1(k10_mcart_1(X4,X3,X2,X1,esk10_0),esk8_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X4,X3,X2,X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | v1_xboole_0(esk9_0)
    | v1_xboole_0(esk7_0)
    | v1_xboole_0(esk6_0)
    | ~ r2_hidden(k10_mcart_1(esk2_0,esk3_0,esk4_0,esk5_0,esk10_0),esk8_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X3,esk7_0,X2,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_43])])).

cnf(c_0_70,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | r2_hidden(k10_mcart_1(X1,X2,X3,X4,esk10_0),esk8_0)
    | v1_xboole_0(esk8_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_68])).

fof(c_0_71,plain,(
    ! [X44] :
      ( ~ v1_xboole_0(X44)
      | X44 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_72,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | v1_xboole_0(esk8_0)
    | v1_xboole_0(esk6_0)
    | v1_xboole_0(esk7_0)
    | v1_xboole_0(esk9_0)
    | ~ m1_subset_1(esk10_0,k4_zfmisc_1(X1,esk7_0,X2,X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_43])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_74,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | v1_xboole_0(esk9_0)
    | v1_xboole_0(esk7_0)
    | v1_xboole_0(esk6_0)
    | v1_xboole_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_47]),c_0_48]),c_0_50]),c_0_51])).

cnf(c_0_75,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk8_0)
    | v1_xboole_0(esk6_0)
    | v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_51])).

fof(c_0_76,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | ~ v1_xboole_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | v1_xboole_0(esk7_0)
    | v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_75]),c_0_50])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | v1_xboole_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_77]),c_0_49])).

fof(c_0_81,plain,(
    ! [X31] : m1_subset_1(esk1_1(X31),X31) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_80]),c_0_48])).

cnf(c_0_84,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_35])])).

cnf(c_0_86,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | v1_xboole_0(esk9_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(X1,esk8_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_88]),c_0_51])).

cnf(c_0_91,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_35])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_93,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_93]),c_0_50])).

cnf(c_0_96,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_35])])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_98,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_86])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_98]),c_0_49])).

cnf(c_0_101,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_100]),c_0_35])])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_86])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_102]),c_0_48]),
    [proof]).

%------------------------------------------------------------------------------
