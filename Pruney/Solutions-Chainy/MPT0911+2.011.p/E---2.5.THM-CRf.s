%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:15 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 825 expanded)
%              Number of clauses        :   59 ( 381 expanded)
%              Number of leaves         :   13 ( 193 expanded)
%              Depth                    :   15
%              Number of atoms          :  215 (3387 expanded)
%              Number of equality atoms :  118 (1974 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X8 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X8 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k7_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_mcart_1])).

fof(c_0_14,plain,(
    ! [X29,X30] :
      ( ( k2_zfmisc_1(X29,X30) != k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | k2_zfmisc_1(X29,X30) = k1_xboole_0 )
      & ( X30 != k1_xboole_0
        | k2_zfmisc_1(X29,X30) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X50,X52,X53,X54,X55] :
      ( ( r2_hidden(esk5_1(X50),X50)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X52,X50)
        | esk5_1(X50) != k4_mcart_1(X52,X53,X54,X55)
        | X50 = k1_xboole_0 )
      & ( ~ r2_hidden(X53,X50)
        | esk5_1(X50) != k4_mcart_1(X52,X53,X54,X55)
        | X50 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_16,negated_conjecture,(
    ! [X71,X72,X73] :
      ( m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X71,esk6_0)
        | ~ m1_subset_1(X72,esk7_0)
        | ~ m1_subset_1(X73,esk8_0)
        | esk10_0 != k3_mcart_1(X71,X72,X73)
        | esk9_0 = X73 )
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k7_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X40,X41,X42] : k3_zfmisc_1(X40,X41,X42) = k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X31,X32] : ~ r2_hidden(X31,k2_zfmisc_1(X31,X32)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X35,X36)
      | v1_xboole_0(X36)
      | r2_hidden(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(esk5_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_1(k2_zfmisc_1(X1,esk8_0)),k2_zfmisc_1(X1,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_1(k2_zfmisc_1(X1,esk7_0)),k2_zfmisc_1(X1,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk5_1(k2_zfmisc_1(X1,esk8_0)),k2_zfmisc_1(X1,esk8_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_1(k2_zfmisc_1(esk6_0,esk7_0)),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_41,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(k1_mcart_1(X47),X48)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) )
      & ( r2_hidden(k2_mcart_1(X47),X49)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_44,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,k2_zfmisc_1(X25,X26))
      | k4_tarski(esk3_1(X24),esk4_1(X24)) = X24 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_47,plain,(
    ! [X64,X65] :
      ( k1_mcart_1(k4_tarski(X64,X65)) = X64
      & k2_mcart_1(k4_tarski(X64,X65)) = X65 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_48,plain,
    ( k4_tarski(esk3_1(X1),esk4_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_50,plain,(
    ! [X56,X57,X58,X59] :
      ( ( k5_mcart_1(X56,X57,X58,X59) = k1_mcart_1(k1_mcart_1(X59))
        | ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 )
      & ( k6_mcart_1(X56,X57,X58,X59) = k2_mcart_1(k1_mcart_1(X59))
        | ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 )
      & ( k7_mcart_1(X56,X57,X58,X59) = k2_mcart_1(X59)
        | ~ m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_51,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k4_tarski(esk3_1(k1_mcart_1(esk10_0)),esk4_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( esk3_1(k1_mcart_1(esk10_0)) = k1_mcart_1(k1_mcart_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_24])).

cnf(c_0_56,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( k4_tarski(esk3_1(esk10_0),esk4_1(esk10_0)) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_46])).

fof(c_0_58,plain,(
    ! [X37,X38,X39] : k3_mcart_1(X37,X38,X39) = k4_tarski(k4_tarski(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_59,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),esk4_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk10_0)) = k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_32]),c_0_27]),c_0_29]),c_0_35])).

fof(c_0_61,plain,(
    ! [X33,X34] :
      ( ~ r2_hidden(X33,X34)
      | m1_subset_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_62,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_63,negated_conjecture,
    ( esk4_1(esk10_0) = k2_mcart_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( esk9_0 = X3
    | ~ m1_subset_1(X1,esk6_0)
    | ~ m1_subset_1(X2,esk7_0)
    | ~ m1_subset_1(X3,esk8_0)
    | esk10_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( esk4_1(k1_mcart_1(esk10_0)) = k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_59]),c_0_60])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_49]),c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_49])).

cnf(c_0_71,negated_conjecture,
    ( k4_tarski(esk3_1(esk10_0),k2_mcart_1(esk10_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_63])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_24])).

cnf(c_0_73,negated_conjecture,
    ( esk9_0 = X3
    | esk10_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk8_0)
    | ~ m1_subset_1(X2,esk7_0)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)) = k1_mcart_1(esk10_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( esk3_1(esk10_0) = k1_mcart_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( esk9_0 != k7_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_80,negated_conjecture,
    ( k7_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) = k2_mcart_1(esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_32]),c_0_27]),c_0_29]),c_0_35])).

cnf(c_0_81,negated_conjecture,
    ( esk9_0 = X1
    | k4_tarski(k1_mcart_1(esk10_0),X1) != esk10_0
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])])).

cnf(c_0_82,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0)) = esk10_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k2_mcart_1(esk10_0) != esk9_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])]),c_0_84]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:38:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.07/1.25  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.07/1.25  # and selection function SelectNegativeLiterals.
% 1.07/1.25  #
% 1.07/1.25  # Preprocessing time       : 0.028 s
% 1.07/1.25  # Presaturation interreduction done
% 1.07/1.25  
% 1.07/1.25  # Proof found!
% 1.07/1.25  # SZS status Theorem
% 1.07/1.25  # SZS output start CNFRefutation
% 1.07/1.25  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 1.07/1.25  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.07/1.25  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 1.07/1.25  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.07/1.25  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.07/1.25  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.07/1.25  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.07/1.25  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.07/1.25  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 1.07/1.25  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.07/1.25  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 1.07/1.25  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 1.07/1.25  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.07/1.25  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 1.07/1.25  fof(c_0_14, plain, ![X29, X30]:((k2_zfmisc_1(X29,X30)!=k1_xboole_0|(X29=k1_xboole_0|X30=k1_xboole_0))&((X29!=k1_xboole_0|k2_zfmisc_1(X29,X30)=k1_xboole_0)&(X30!=k1_xboole_0|k2_zfmisc_1(X29,X30)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.07/1.25  fof(c_0_15, plain, ![X50, X52, X53, X54, X55]:((r2_hidden(esk5_1(X50),X50)|X50=k1_xboole_0)&((~r2_hidden(X52,X50)|esk5_1(X50)!=k4_mcart_1(X52,X53,X54,X55)|X50=k1_xboole_0)&(~r2_hidden(X53,X50)|esk5_1(X50)!=k4_mcart_1(X52,X53,X54,X55)|X50=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 1.07/1.25  fof(c_0_16, negated_conjecture, ![X71, X72, X73]:(m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X71,esk6_0)|(~m1_subset_1(X72,esk7_0)|(~m1_subset_1(X73,esk8_0)|(esk10_0!=k3_mcart_1(X71,X72,X73)|esk9_0=X73))))&(((esk6_0!=k1_xboole_0&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k7_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 1.07/1.25  fof(c_0_17, plain, ![X40, X41, X42]:k3_zfmisc_1(X40,X41,X42)=k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 1.07/1.25  fof(c_0_18, plain, ![X31, X32]:~r2_hidden(X31,k2_zfmisc_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 1.07/1.25  cnf(c_0_19, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.25  cnf(c_0_20, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.07/1.25  cnf(c_0_21, plain, (r2_hidden(esk5_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.07/1.25  fof(c_0_22, plain, ![X35, X36]:(~m1_subset_1(X35,X36)|(v1_xboole_0(X36)|r2_hidden(X35,X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 1.07/1.25  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  cnf(c_0_24, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.07/1.25  cnf(c_0_25, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.07/1.25  cnf(c_0_26, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_19])).
% 1.07/1.25  cnf(c_0_27, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  cnf(c_0_28, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(esk5_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.07/1.25  cnf(c_0_29, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  fof(c_0_30, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.07/1.25  cnf(c_0_31, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.07/1.25  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 1.07/1.25  cnf(c_0_33, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.07/1.25  cnf(c_0_34, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk5_1(k2_zfmisc_1(X1,esk8_0)),k2_zfmisc_1(X1,esk8_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.07/1.25  cnf(c_0_35, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  cnf(c_0_36, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk5_1(k2_zfmisc_1(X1,esk7_0)),k2_zfmisc_1(X1,esk7_0))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 1.07/1.25  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.07/1.25  cnf(c_0_38, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.07/1.25  cnf(c_0_39, negated_conjecture, (r2_hidden(esk5_1(k2_zfmisc_1(X1,esk8_0)),k2_zfmisc_1(X1,esk8_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.07/1.25  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_1(k2_zfmisc_1(esk6_0,esk7_0)),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.07/1.25  fof(c_0_41, plain, ![X47, X48, X49]:((r2_hidden(k1_mcart_1(X47),X48)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))&(r2_hidden(k2_mcart_1(X47),X49)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 1.07/1.25  cnf(c_0_42, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.07/1.25  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_1(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)),k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.07/1.25  fof(c_0_44, plain, ![X24, X25, X26]:(~r2_hidden(X24,k2_zfmisc_1(X25,X26))|k4_tarski(esk3_1(X24),esk4_1(X24))=X24), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 1.07/1.25  cnf(c_0_45, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.07/1.25  cnf(c_0_46, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.07/1.25  fof(c_0_47, plain, ![X64, X65]:(k1_mcart_1(k4_tarski(X64,X65))=X64&k2_mcart_1(k4_tarski(X64,X65))=X65), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 1.07/1.25  cnf(c_0_48, plain, (k4_tarski(esk3_1(X1),esk4_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.07/1.25  cnf(c_0_49, negated_conjecture, (r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.07/1.25  fof(c_0_50, plain, ![X56, X57, X58, X59]:(((k5_mcart_1(X56,X57,X58,X59)=k1_mcart_1(k1_mcart_1(X59))|~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|(X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0))&(k6_mcart_1(X56,X57,X58,X59)=k2_mcart_1(k1_mcart_1(X59))|~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|(X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0)))&(k7_mcart_1(X56,X57,X58,X59)=k2_mcart_1(X59)|~m1_subset_1(X59,k3_zfmisc_1(X56,X57,X58))|(X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 1.07/1.25  cnf(c_0_51, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.07/1.25  cnf(c_0_52, negated_conjecture, (k4_tarski(esk3_1(k1_mcart_1(esk10_0)),esk4_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.07/1.25  cnf(c_0_53, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.07/1.25  cnf(c_0_54, negated_conjecture, (esk3_1(k1_mcart_1(esk10_0))=k1_mcart_1(k1_mcart_1(esk10_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 1.07/1.25  cnf(c_0_55, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_53, c_0_24])).
% 1.07/1.25  cnf(c_0_56, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_47])).
% 1.07/1.25  cnf(c_0_57, negated_conjecture, (k4_tarski(esk3_1(esk10_0),esk4_1(esk10_0))=esk10_0), inference(spm,[status(thm)],[c_0_48, c_0_46])).
% 1.07/1.25  fof(c_0_58, plain, ![X37, X38, X39]:k3_mcart_1(X37,X38,X39)=k4_tarski(k4_tarski(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 1.07/1.25  cnf(c_0_59, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),esk4_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)), inference(rw,[status(thm)],[c_0_52, c_0_54])).
% 1.07/1.25  cnf(c_0_60, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk10_0))=k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_32]), c_0_27]), c_0_29]), c_0_35])).
% 1.07/1.25  fof(c_0_61, plain, ![X33, X34]:(~r2_hidden(X33,X34)|m1_subset_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 1.07/1.25  cnf(c_0_62, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.07/1.25  cnf(c_0_63, negated_conjecture, (esk4_1(esk10_0)=k2_mcart_1(esk10_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.07/1.25  cnf(c_0_64, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.07/1.25  cnf(c_0_65, negated_conjecture, (esk9_0=X3|~m1_subset_1(X1,esk6_0)|~m1_subset_1(X2,esk7_0)|~m1_subset_1(X3,esk8_0)|esk10_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  cnf(c_0_66, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.07/1.25  cnf(c_0_67, negated_conjecture, (esk4_1(k1_mcart_1(esk10_0))=k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_59]), c_0_60])).
% 1.07/1.25  cnf(c_0_68, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.07/1.25  cnf(c_0_69, negated_conjecture, (r2_hidden(k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_49]), c_0_60])).
% 1.07/1.25  cnf(c_0_70, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_49])).
% 1.07/1.25  cnf(c_0_71, negated_conjecture, (k4_tarski(esk3_1(esk10_0),k2_mcart_1(esk10_0))=esk10_0), inference(rw,[status(thm)],[c_0_57, c_0_63])).
% 1.07/1.25  cnf(c_0_72, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_64, c_0_24])).
% 1.07/1.25  cnf(c_0_73, negated_conjecture, (esk9_0=X3|esk10_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk8_0)|~m1_subset_1(X2,esk7_0)|~m1_subset_1(X1,esk6_0)), inference(rw,[status(thm)],[c_0_65, c_0_66])).
% 1.07/1.25  cnf(c_0_74, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0))=k1_mcart_1(esk10_0)), inference(rw,[status(thm)],[c_0_59, c_0_67])).
% 1.07/1.25  cnf(c_0_75, negated_conjecture, (m1_subset_1(k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0),esk7_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 1.07/1.25  cnf(c_0_76, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_70])).
% 1.07/1.25  cnf(c_0_77, negated_conjecture, (esk3_1(esk10_0)=k1_mcart_1(esk10_0)), inference(spm,[status(thm)],[c_0_51, c_0_71])).
% 1.07/1.25  cnf(c_0_78, negated_conjecture, (r2_hidden(k2_mcart_1(esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_62, c_0_46])).
% 1.07/1.25  cnf(c_0_79, negated_conjecture, (esk9_0!=k7_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.07/1.25  cnf(c_0_80, negated_conjecture, (k7_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)=k2_mcart_1(esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_32]), c_0_27]), c_0_29]), c_0_35])).
% 1.07/1.25  cnf(c_0_81, negated_conjecture, (esk9_0=X1|k4_tarski(k1_mcart_1(esk10_0),X1)!=esk10_0|~m1_subset_1(X1,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])])).
% 1.07/1.25  cnf(c_0_82, negated_conjecture, (k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0))=esk10_0), inference(rw,[status(thm)],[c_0_71, c_0_77])).
% 1.07/1.25  cnf(c_0_83, negated_conjecture, (m1_subset_1(k2_mcart_1(esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_68, c_0_78])).
% 1.07/1.25  cnf(c_0_84, negated_conjecture, (k2_mcart_1(esk10_0)!=esk9_0), inference(rw,[status(thm)],[c_0_79, c_0_80])).
% 1.07/1.25  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])]), c_0_84]), ['proof']).
% 1.07/1.25  # SZS output end CNFRefutation
% 1.07/1.25  # Proof object total steps             : 86
% 1.07/1.25  # Proof object clause steps            : 59
% 1.07/1.25  # Proof object formula steps           : 27
% 1.07/1.25  # Proof object conjectures             : 41
% 1.07/1.25  # Proof object clause conjectures      : 38
% 1.07/1.25  # Proof object formula conjectures     : 3
% 1.07/1.25  # Proof object initial clauses used    : 22
% 1.07/1.25  # Proof object initial formulas used   : 13
% 1.07/1.25  # Proof object generating inferences   : 27
% 1.07/1.25  # Proof object simplifying inferences  : 24
% 1.07/1.25  # Training examples: 0 positive, 0 negative
% 1.07/1.25  # Parsed axioms                        : 17
% 1.07/1.25  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.25  # Initial clauses                      : 40
% 1.07/1.25  # Removed in clause preprocessing      : 4
% 1.07/1.25  # Initial clauses in saturation        : 36
% 1.07/1.25  # Processed clauses                    : 5265
% 1.07/1.25  # ...of these trivial                  : 1251
% 1.07/1.25  # ...subsumed                          : 3147
% 1.07/1.25  # ...remaining for further processing  : 867
% 1.07/1.25  # Other redundant clauses eliminated   : 763
% 1.07/1.25  # Clauses deleted for lack of memory   : 0
% 1.07/1.25  # Backward-subsumed                    : 3
% 1.07/1.25  # Backward-rewritten                   : 43
% 1.07/1.25  # Generated clauses                    : 136050
% 1.07/1.25  # ...of the previous two non-trivial   : 98773
% 1.07/1.25  # Contextual simplify-reflections      : 3
% 1.07/1.25  # Paramodulations                      : 135053
% 1.07/1.25  # Factorizations                       : 236
% 1.07/1.25  # Equation resolutions                 : 763
% 1.07/1.25  # Propositional unsat checks           : 0
% 1.07/1.25  #    Propositional check models        : 0
% 1.07/1.25  #    Propositional check unsatisfiable : 0
% 1.07/1.25  #    Propositional clauses             : 0
% 1.07/1.25  #    Propositional clauses after purity: 0
% 1.07/1.25  #    Propositional unsat core size     : 0
% 1.07/1.25  #    Propositional preprocessing time  : 0.000
% 1.07/1.25  #    Propositional encoding time       : 0.000
% 1.07/1.25  #    Propositional solver time         : 0.000
% 1.07/1.25  #    Success case prop preproc time    : 0.000
% 1.07/1.25  #    Success case prop encoding time   : 0.000
% 1.07/1.25  #    Success case prop solver time     : 0.000
% 1.07/1.25  # Current number of processed clauses  : 780
% 1.07/1.25  #    Positive orientable unit clauses  : 400
% 1.07/1.25  #    Positive unorientable unit clauses: 0
% 1.07/1.25  #    Negative unit clauses             : 6
% 1.07/1.25  #    Non-unit-clauses                  : 374
% 1.07/1.25  # Current number of unprocessed clauses: 93310
% 1.07/1.25  # ...number of literals in the above   : 442307
% 1.07/1.25  # Current number of archived formulas  : 0
% 1.07/1.25  # Current number of archived clauses   : 82
% 1.07/1.25  # Clause-clause subsumption calls (NU) : 31125
% 1.07/1.25  # Rec. Clause-clause subsumption calls : 21195
% 1.07/1.25  # Non-unit clause-clause subsumptions  : 3100
% 1.07/1.25  # Unit Clause-clause subsumption calls : 1160
% 1.07/1.25  # Rewrite failures with RHS unbound    : 0
% 1.07/1.25  # BW rewrite match attempts            : 1201
% 1.07/1.25  # BW rewrite match successes           : 25
% 1.07/1.25  # Condensation attempts                : 0
% 1.07/1.25  # Condensation successes               : 0
% 1.07/1.25  # Termbank termtop insertions          : 2216664
% 1.07/1.25  
% 1.07/1.25  # -------------------------------------------------
% 1.07/1.25  # User time                : 0.870 s
% 1.07/1.25  # System time              : 0.045 s
% 1.07/1.25  # Total time               : 0.915 s
% 1.07/1.25  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
