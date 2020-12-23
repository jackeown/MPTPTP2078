%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:13 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 303 expanded)
%              Number of clauses        :   55 ( 129 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 (1345 expanded)
%              Number of equality atoms :  162 ( 874 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   15 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

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

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

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
    ! [X31,X32,X33,X34] : k4_zfmisc_1(X31,X32,X33,X34) = k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X28,X29,X30] : k3_zfmisc_1(X28,X29,X30) = k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X39,X40,X41] :
      ( ( r2_hidden(k1_mcart_1(X39),X40)
        | ~ r2_hidden(X39,k2_zfmisc_1(X40,X41)) )
      & ( r2_hidden(k2_mcart_1(X39),X41)
        | ~ r2_hidden(X39,k2_zfmisc_1(X40,X41)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

fof(c_0_17,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X23,X24)
      | v1_xboole_0(X24)
      | r2_hidden(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_18,negated_conjecture,(
    ! [X65,X66,X67] :
      ( m1_subset_1(esk9_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))
      & ( ~ m1_subset_1(X65,esk5_0)
        | ~ m1_subset_1(X66,esk6_0)
        | ~ m1_subset_1(X67,esk7_0)
        | esk9_0 != k3_mcart_1(X65,X66,X67)
        | esk8_0 = X67 )
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k7_mcart_1(esk5_0,esk6_0,esk7_0,esk9_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_19,plain,(
    ! [X56,X57,X58,X59] :
      ( ( X56 = k1_xboole_0
        | X57 = k1_xboole_0
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | k4_zfmisc_1(X56,X57,X58,X59) != k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k4_zfmisc_1(X56,X57,X58,X59) = k1_xboole_0 )
      & ( X57 != k1_xboole_0
        | k4_zfmisc_1(X56,X57,X58,X59) = k1_xboole_0 )
      & ( X58 != k1_xboole_0
        | k4_zfmisc_1(X56,X57,X58,X59) = k1_xboole_0 )
      & ( X59 != k1_xboole_0
        | k4_zfmisc_1(X56,X57,X58,X59) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_20,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X42,X44,X45,X46,X47] :
      ( ( r2_hidden(esk4_1(X42),X42)
        | X42 = k1_xboole_0 )
      & ( ~ r2_hidden(X44,X42)
        | esk4_1(X42) != k4_mcart_1(X44,X45,X46,X47)
        | X42 = k1_xboole_0 )
      & ( ~ r2_hidden(X45,X42)
        | esk4_1(X42) != k4_mcart_1(X44,X45,X46,X47)
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk9_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X48,X49,X50,X51] :
      ( X48 = k1_xboole_0
      | X49 = k1_xboole_0
      | X50 = k1_xboole_0
      | ~ m1_subset_1(X51,k3_zfmisc_1(X48,X49,X50))
      | X51 = k3_mcart_1(k5_mcart_1(X48,X49,X50,X51),k6_mcart_1(X48,X49,X50,X51),k7_mcart_1(X48,X49,X50,X51)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

fof(c_0_31,plain,(
    ! [X25,X26,X27] : k3_mcart_1(X25,X26,X27) = k4_tarski(k4_tarski(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_32,plain,(
    ! [X52,X53,X54,X55] :
      ( ( k5_mcart_1(X52,X53,X54,X55) = k1_mcart_1(k1_mcart_1(X55))
        | ~ m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 )
      & ( k6_mcart_1(X52,X53,X54,X55) = k2_mcart_1(k1_mcart_1(X55))
        | ~ m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 )
      & ( k7_mcart_1(X52,X53,X54,X55) = k2_mcart_1(X55)
        | ~ m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))
        | X52 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | v1_xboole_0(k2_zfmisc_1(X2,X3))
    | ~ m1_subset_1(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | X4 = k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_21])).

cnf(c_0_47,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_21])).

cnf(c_0_48,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_49,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))
      | m1_subset_1(k7_mcart_1(X35,X36,X37,X38),X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

cnf(c_0_50,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_42,c_0_28])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k2_mcart_1(X4)) = X4
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_21])).

cnf(c_0_58,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_59,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_61,plain,
    ( k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k2_mcart_1(k1_mcart_1(X4))),k2_mcart_1(X4)) = X4
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_21])).

cnf(c_0_63,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_21])).

fof(c_0_64,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | m1_subset_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_65,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( esk8_0 = X3
    | ~ m1_subset_1(X1,esk5_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X3,esk7_0)
    | esk9_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X1)),k2_mcart_1(k1_mcart_1(X1))),k2_mcart_1(X1)) = X1
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(X4),X3)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_47])).

cnf(c_0_70,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk9_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk9_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( esk8_0 = X3
    | esk9_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_67,c_0_40])).

cnf(c_0_74,negated_conjecture,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk9_0)),k2_mcart_1(k1_mcart_1(esk9_0))),k2_mcart_1(esk9_0)) = esk9_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_36]),c_0_55]),c_0_54]),c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk9_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_36]),c_0_55]),c_0_54]),c_0_53])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk9_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk9_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( esk8_0 != k7_mcart_1(esk5_0,esk6_0,esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,negated_conjecture,
    ( esk8_0 = k2_mcart_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76]),c_0_77])])).

cnf(c_0_80,negated_conjecture,
    ( k7_mcart_1(esk5_0,esk6_0,esk7_0,esk9_0) != k2_mcart_1(esk9_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_47]),c_0_36])]),c_0_53]),c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 2.73/2.89  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 2.73/2.89  # and selection function SelectMaxLComplexAvoidPosPred.
% 2.73/2.89  #
% 2.73/2.89  # Preprocessing time       : 0.028 s
% 2.73/2.89  # Presaturation interreduction done
% 2.73/2.89  
% 2.73/2.89  # Proof found!
% 2.73/2.89  # SZS status Theorem
% 2.73/2.89  # SZS output start CNFRefutation
% 2.73/2.89  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 2.73/2.89  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 2.73/2.89  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.73/2.89  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.73/2.89  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.73/2.89  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 2.73/2.89  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.73/2.89  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 2.73/2.89  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.73/2.89  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.73/2.89  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.73/2.89  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 2.73/2.89  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.73/2.89  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 2.73/2.89  fof(c_0_14, plain, ![X31, X32, X33, X34]:k4_zfmisc_1(X31,X32,X33,X34)=k2_zfmisc_1(k3_zfmisc_1(X31,X32,X33),X34), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 2.73/2.89  fof(c_0_15, plain, ![X28, X29, X30]:k3_zfmisc_1(X28,X29,X30)=k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 2.73/2.89  fof(c_0_16, plain, ![X39, X40, X41]:((r2_hidden(k1_mcart_1(X39),X40)|~r2_hidden(X39,k2_zfmisc_1(X40,X41)))&(r2_hidden(k2_mcart_1(X39),X41)|~r2_hidden(X39,k2_zfmisc_1(X40,X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 2.73/2.89  fof(c_0_17, plain, ![X23, X24]:(~m1_subset_1(X23,X24)|(v1_xboole_0(X24)|r2_hidden(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 2.73/2.89  fof(c_0_18, negated_conjecture, ![X65, X66, X67]:(m1_subset_1(esk9_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))&((~m1_subset_1(X65,esk5_0)|(~m1_subset_1(X66,esk6_0)|(~m1_subset_1(X67,esk7_0)|(esk9_0!=k3_mcart_1(X65,X66,X67)|esk8_0=X67))))&(((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&esk7_0!=k1_xboole_0)&esk8_0!=k7_mcart_1(esk5_0,esk6_0,esk7_0,esk9_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 2.73/2.89  fof(c_0_19, plain, ![X56, X57, X58, X59]:((X56=k1_xboole_0|X57=k1_xboole_0|X58=k1_xboole_0|X59=k1_xboole_0|k4_zfmisc_1(X56,X57,X58,X59)!=k1_xboole_0)&((((X56!=k1_xboole_0|k4_zfmisc_1(X56,X57,X58,X59)=k1_xboole_0)&(X57!=k1_xboole_0|k4_zfmisc_1(X56,X57,X58,X59)=k1_xboole_0))&(X58!=k1_xboole_0|k4_zfmisc_1(X56,X57,X58,X59)=k1_xboole_0))&(X59!=k1_xboole_0|k4_zfmisc_1(X56,X57,X58,X59)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 2.73/2.89  cnf(c_0_20, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.73/2.89  cnf(c_0_21, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.73/2.89  fof(c_0_22, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 2.73/2.89  fof(c_0_23, plain, ![X42, X44, X45, X46, X47]:((r2_hidden(esk4_1(X42),X42)|X42=k1_xboole_0)&((~r2_hidden(X44,X42)|esk4_1(X42)!=k4_mcart_1(X44,X45,X46,X47)|X42=k1_xboole_0)&(~r2_hidden(X45,X42)|esk4_1(X42)!=k4_mcart_1(X44,X45,X46,X47)|X42=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 2.73/2.89  cnf(c_0_24, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.73/2.89  cnf(c_0_25, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.73/2.89  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk9_0,k3_zfmisc_1(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.73/2.89  cnf(c_0_27, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.73/2.89  cnf(c_0_28, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 2.73/2.89  cnf(c_0_29, plain, (k4_zfmisc_1(X2,X3,X4,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.73/2.89  fof(c_0_30, plain, ![X48, X49, X50, X51]:(X48=k1_xboole_0|X49=k1_xboole_0|X50=k1_xboole_0|(~m1_subset_1(X51,k3_zfmisc_1(X48,X49,X50))|X51=k3_mcart_1(k5_mcart_1(X48,X49,X50,X51),k6_mcart_1(X48,X49,X50,X51),k7_mcart_1(X48,X49,X50,X51)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 2.73/2.89  fof(c_0_31, plain, ![X25, X26, X27]:k3_mcart_1(X25,X26,X27)=k4_tarski(k4_tarski(X25,X26),X27), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 2.73/2.89  fof(c_0_32, plain, ![X52, X53, X54, X55]:(((k5_mcart_1(X52,X53,X54,X55)=k1_mcart_1(k1_mcart_1(X55))|~m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))|(X52=k1_xboole_0|X53=k1_xboole_0|X54=k1_xboole_0))&(k6_mcart_1(X52,X53,X54,X55)=k2_mcart_1(k1_mcart_1(X55))|~m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))|(X52=k1_xboole_0|X53=k1_xboole_0|X54=k1_xboole_0)))&(k7_mcart_1(X52,X53,X54,X55)=k2_mcart_1(X55)|~m1_subset_1(X55,k3_zfmisc_1(X52,X53,X54))|(X52=k1_xboole_0|X53=k1_xboole_0|X54=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 2.73/2.89  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.73/2.89  cnf(c_0_34, plain, (r2_hidden(esk4_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.73/2.89  cnf(c_0_35, plain, (r2_hidden(k1_mcart_1(X1),X2)|v1_xboole_0(k2_zfmisc_1(X2,X3))|~m1_subset_1(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 2.73/2.89  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk9_0,k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(rw,[status(thm)],[c_0_26, c_0_21])).
% 2.73/2.89  cnf(c_0_37, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 2.73/2.89  cnf(c_0_38, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 2.73/2.89  cnf(c_0_39, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.73/2.89  cnf(c_0_40, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.73/2.89  cnf(c_0_41, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.73/2.89  cnf(c_0_42, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.73/2.89  cnf(c_0_43, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 2.73/2.89  cnf(c_0_44, negated_conjecture, (r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.73/2.89  cnf(c_0_45, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.73/2.89  cnf(c_0_46, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|X4=k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_21])).
% 2.73/2.89  cnf(c_0_47, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_41, c_0_21])).
% 2.73/2.89  cnf(c_0_48, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.73/2.89  fof(c_0_49, plain, ![X35, X36, X37, X38]:(~m1_subset_1(X38,k3_zfmisc_1(X35,X36,X37))|m1_subset_1(k7_mcart_1(X35,X36,X37,X38),X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 2.73/2.89  cnf(c_0_50, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_42, c_0_28])).
% 2.73/2.89  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 2.73/2.89  cnf(c_0_52, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_45])).
% 2.73/2.89  cnf(c_0_53, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.73/2.89  cnf(c_0_54, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.73/2.89  cnf(c_0_55, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.73/2.89  cnf(c_0_56, plain, (k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4)),k2_mcart_1(X4))=X4|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.73/2.89  cnf(c_0_57, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_48, c_0_21])).
% 2.73/2.89  cnf(c_0_58, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.73/2.89  cnf(c_0_59, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 2.73/2.89  cnf(c_0_60, negated_conjecture, (X1=k1_xboole_0|r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])]), c_0_53]), c_0_54]), c_0_55])).
% 2.73/2.89  cnf(c_0_61, plain, (k4_tarski(k4_tarski(k5_mcart_1(X1,X2,X3,X4),k2_mcart_1(k1_mcart_1(X4))),k2_mcart_1(X4))=X4|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 2.73/2.89  cnf(c_0_62, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_58, c_0_21])).
% 2.73/2.89  cnf(c_0_63, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_59, c_0_21])).
% 2.73/2.89  fof(c_0_64, plain, ![X21, X22]:(~r2_hidden(X21,X22)|m1_subset_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 2.73/2.89  cnf(c_0_65, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.73/2.89  cnf(c_0_66, negated_conjecture, (r2_hidden(k1_mcart_1(esk9_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_60])).
% 2.73/2.89  cnf(c_0_67, negated_conjecture, (esk8_0=X3|~m1_subset_1(X1,esk5_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X3,esk7_0)|esk9_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.73/2.89  cnf(c_0_68, plain, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(X1)),k2_mcart_1(k1_mcart_1(X1))),k2_mcart_1(X1))=X1|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 2.73/2.89  cnf(c_0_69, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|m1_subset_1(k2_mcart_1(X4),X3)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(spm,[status(thm)],[c_0_63, c_0_47])).
% 2.73/2.89  cnf(c_0_70, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 2.73/2.89  cnf(c_0_71, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk9_0)),esk6_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.73/2.89  cnf(c_0_72, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk9_0)),esk5_0)), inference(spm,[status(thm)],[c_0_24, c_0_66])).
% 2.73/2.89  cnf(c_0_73, negated_conjecture, (esk8_0=X3|esk9_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk7_0)|~m1_subset_1(X2,esk6_0)|~m1_subset_1(X1,esk5_0)), inference(rw,[status(thm)],[c_0_67, c_0_40])).
% 2.73/2.89  cnf(c_0_74, negated_conjecture, (k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk9_0)),k2_mcart_1(k1_mcart_1(esk9_0))),k2_mcart_1(esk9_0))=esk9_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_36]), c_0_55]), c_0_54]), c_0_53])).
% 2.73/2.89  cnf(c_0_75, negated_conjecture, (m1_subset_1(k2_mcart_1(esk9_0),esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_36]), c_0_55]), c_0_54]), c_0_53])).
% 2.73/2.89  cnf(c_0_76, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk9_0)),esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 2.73/2.89  cnf(c_0_77, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk9_0)),esk5_0)), inference(spm,[status(thm)],[c_0_70, c_0_72])).
% 2.73/2.89  cnf(c_0_78, negated_conjecture, (esk8_0!=k7_mcart_1(esk5_0,esk6_0,esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.73/2.89  cnf(c_0_79, negated_conjecture, (esk8_0=k2_mcart_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76]), c_0_77])])).
% 2.73/2.89  cnf(c_0_80, negated_conjecture, (k7_mcart_1(esk5_0,esk6_0,esk7_0,esk9_0)!=k2_mcart_1(esk9_0)), inference(rw,[status(thm)],[c_0_78, c_0_79])).
% 2.73/2.89  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_47]), c_0_36])]), c_0_53]), c_0_54]), c_0_55]), ['proof']).
% 2.73/2.89  # SZS output end CNFRefutation
% 2.73/2.89  # Proof object total steps             : 82
% 2.73/2.89  # Proof object clause steps            : 55
% 2.73/2.89  # Proof object formula steps           : 27
% 2.73/2.89  # Proof object conjectures             : 24
% 2.73/2.89  # Proof object clause conjectures      : 21
% 2.73/2.89  # Proof object formula conjectures     : 3
% 2.73/2.89  # Proof object initial clauses used    : 23
% 2.73/2.89  # Proof object initial formulas used   : 13
% 2.73/2.89  # Proof object generating inferences   : 20
% 2.73/2.89  # Proof object simplifying inferences  : 33
% 2.73/2.89  # Training examples: 0 positive, 0 negative
% 2.73/2.89  # Parsed axioms                        : 15
% 2.73/2.89  # Removed by relevancy pruning/SinE    : 0
% 2.73/2.89  # Initial clauses                      : 34
% 2.73/2.89  # Removed in clause preprocessing      : 3
% 2.73/2.89  # Initial clauses in saturation        : 31
% 2.73/2.89  # Processed clauses                    : 67695
% 2.73/2.89  # ...of these trivial                  : 82
% 2.73/2.89  # ...subsumed                          : 64423
% 2.73/2.89  # ...remaining for further processing  : 3190
% 2.73/2.89  # Other redundant clauses eliminated   : 41
% 2.73/2.89  # Clauses deleted for lack of memory   : 0
% 2.73/2.89  # Backward-subsumed                    : 54
% 2.73/2.89  # Backward-rewritten                   : 321
% 2.73/2.89  # Generated clauses                    : 303141
% 2.73/2.89  # ...of the previous two non-trivial   : 279327
% 2.73/2.89  # Contextual simplify-reflections      : 165
% 2.73/2.89  # Paramodulations                      : 303038
% 2.73/2.89  # Factorizations                       : 42
% 2.73/2.89  # Equation resolutions                 : 61
% 2.73/2.89  # Propositional unsat checks           : 0
% 2.73/2.89  #    Propositional check models        : 0
% 2.73/2.89  #    Propositional check unsatisfiable : 0
% 2.73/2.89  #    Propositional clauses             : 0
% 2.73/2.89  #    Propositional clauses after purity: 0
% 2.73/2.89  #    Propositional unsat core size     : 0
% 2.73/2.89  #    Propositional preprocessing time  : 0.000
% 2.73/2.89  #    Propositional encoding time       : 0.000
% 2.73/2.89  #    Propositional solver time         : 0.000
% 2.73/2.89  #    Success case prop preproc time    : 0.000
% 2.73/2.89  #    Success case prop encoding time   : 0.000
% 2.73/2.89  #    Success case prop solver time     : 0.000
% 2.73/2.89  # Current number of processed clauses  : 2783
% 2.73/2.89  #    Positive orientable unit clauses  : 13
% 2.73/2.89  #    Positive unorientable unit clauses: 0
% 2.73/2.89  #    Negative unit clauses             : 8
% 2.73/2.89  #    Non-unit-clauses                  : 2762
% 2.73/2.89  # Current number of unprocessed clauses: 210015
% 2.73/2.89  # ...number of literals in the above   : 687758
% 2.73/2.89  # Current number of archived formulas  : 0
% 2.73/2.89  # Current number of archived clauses   : 408
% 2.73/2.89  # Clause-clause subsumption calls (NU) : 2007454
% 2.73/2.89  # Rec. Clause-clause subsumption calls : 1481203
% 2.73/2.89  # Non-unit clause-clause subsumptions  : 64600
% 2.73/2.89  # Unit Clause-clause subsumption calls : 2677
% 2.73/2.89  # Rewrite failures with RHS unbound    : 0
% 2.73/2.89  # BW rewrite match attempts            : 11
% 2.73/2.89  # BW rewrite match successes           : 11
% 2.73/2.89  # Condensation attempts                : 0
% 2.73/2.89  # Condensation successes               : 0
% 2.73/2.89  # Termbank termtop insertions          : 5533726
% 2.73/2.90  
% 2.73/2.90  # -------------------------------------------------
% 2.73/2.90  # User time                : 2.458 s
% 2.73/2.90  # System time              : 0.102 s
% 2.73/2.90  # Total time               : 2.560 s
% 2.73/2.90  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
