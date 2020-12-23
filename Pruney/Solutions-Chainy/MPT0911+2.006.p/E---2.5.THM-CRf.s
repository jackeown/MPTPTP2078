%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:14 EST 2020

% Result     : Theorem 10.77s
% Output     : CNFRefutation 10.77s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 836 expanded)
%              Number of clauses        :   58 ( 400 expanded)
%              Number of leaves         :   11 ( 193 expanded)
%              Depth                    :   17
%              Number of atoms          :  239 (4014 expanded)
%              Number of equality atoms :  105 (1703 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(l139_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & ! [X4,X5] : k4_tarski(X4,X5) != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

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

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16,X19,X20,X21,X22,X23,X24,X26,X27] :
      ( ( r2_hidden(esk2_4(X13,X14,X15,X16),X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( r2_hidden(esk3_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( X16 = k4_tarski(esk2_4(X13,X14,X15,X16),esk3_4(X13,X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( ~ r2_hidden(X20,X13)
        | ~ r2_hidden(X21,X14)
        | X19 != k4_tarski(X20,X21)
        | r2_hidden(X19,X15)
        | X15 != k2_zfmisc_1(X13,X14) )
      & ( ~ r2_hidden(esk4_3(X22,X23,X24),X24)
        | ~ r2_hidden(X26,X22)
        | ~ r2_hidden(X27,X23)
        | esk4_3(X22,X23,X24) != k4_tarski(X26,X27)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk5_3(X22,X23,X24),X22)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( r2_hidden(esk6_3(X22,X23,X24),X23)
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) )
      & ( esk4_3(X22,X23,X24) = k4_tarski(esk5_3(X22,X23,X24),esk6_3(X22,X23,X24))
        | r2_hidden(esk4_3(X22,X23,X24),X24)
        | X24 = k2_zfmisc_1(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_13,negated_conjecture,(
    ! [X77,X78,X79] :
      ( m1_subset_1(esk14_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))
      & ( ~ m1_subset_1(X77,esk10_0)
        | ~ m1_subset_1(X78,esk11_0)
        | ~ m1_subset_1(X79,esk12_0)
        | esk14_0 != k3_mcart_1(X77,X78,X79)
        | esk13_0 = X79 )
      & esk10_0 != k1_xboole_0
      & esk11_0 != k1_xboole_0
      & esk12_0 != k1_xboole_0
      & esk13_0 != k7_mcart_1(esk10_0,esk11_0,esk12_0,esk14_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X56,X58,X59,X60,X61] :
      ( ( r2_hidden(esk9_1(X56),X56)
        | X56 = k1_xboole_0 )
      & ( ~ r2_hidden(X58,X56)
        | esk9_1(X56) != k4_mcart_1(X58,X59,X60,X61)
        | X56 = k1_xboole_0 )
      & ( ~ r2_hidden(X59,X56)
        | esk9_1(X56) != k4_mcart_1(X58,X59,X60,X61)
        | X56 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk9_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X40,X41,X42] : k3_zfmisc_1(X40,X41,X42) = k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk9_1(esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( esk11_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk14_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( esk12_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_1(esk10_0),X1),k2_zfmisc_1(esk10_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk9_1(esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk9_1(esk12_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_1(esk10_0),esk9_1(esk11_0)),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk9_1(esk12_0)),k2_zfmisc_1(X2,esk12_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_1(k2_zfmisc_1(esk10_0,esk11_0)),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_39,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(k1_mcart_1(X47),X48)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) )
      & ( r2_hidden(k2_mcart_1(X47),X49)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_1(k2_zfmisc_1(esk10_0,esk11_0)),esk9_1(esk12_0)),k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,k2_zfmisc_1(X31,X32))
      | k4_tarski(esk7_1(X30),esk8_1(X30)) = X30 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_45,plain,(
    ! [X70,X71] :
      ( k1_mcart_1(k4_tarski(X70,X71)) = X70
      & k2_mcart_1(k4_tarski(X70,X71)) = X71 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_46,plain,
    ( k4_tarski(esk7_1(X1),esk8_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk14_0),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k4_tarski(esk7_1(k1_mcart_1(esk14_0)),esk8_1(k1_mcart_1(esk14_0))) = k1_mcart_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( esk7_1(k1_mcart_1(esk14_0)) = k1_mcart_1(k1_mcart_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( k4_tarski(esk7_1(esk14_0),esk8_1(esk14_0)) = esk14_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_44])).

fof(c_0_52,plain,(
    ! [X62,X63,X64,X65] :
      ( ( k5_mcart_1(X62,X63,X64,X65) = k1_mcart_1(k1_mcart_1(X65))
        | ~ m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0 )
      & ( k6_mcart_1(X62,X63,X64,X65) = k2_mcart_1(k1_mcart_1(X65))
        | ~ m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0 )
      & ( k7_mcart_1(X62,X63,X64,X65) = k2_mcart_1(X65)
        | ~ m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))
        | X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_53,plain,(
    ! [X37,X38,X39] : k3_mcart_1(X37,X38,X39) = k4_tarski(k4_tarski(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_54,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk14_0)),esk8_1(k1_mcart_1(esk14_0))) = k1_mcart_1(esk14_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( esk7_1(esk14_0) = k1_mcart_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_51])).

cnf(c_0_59,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( esk13_0 = X3
    | ~ m1_subset_1(X1,esk10_0)
    | ~ m1_subset_1(X2,esk11_0)
    | ~ m1_subset_1(X3,esk12_0)
    | esk14_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( esk8_1(k1_mcart_1(esk14_0)) = k2_mcart_1(k1_mcart_1(esk14_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(esk14_0)),esk11_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk14_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_47])).

cnf(c_0_66,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk14_0),esk8_1(esk14_0)) = esk14_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_58])).

cnf(c_0_67,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_25])).

cnf(c_0_68,negated_conjecture,
    ( esk13_0 = X3
    | esk14_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk12_0)
    | ~ m1_subset_1(X2,esk11_0)
    | ~ m1_subset_1(X1,esk10_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk14_0)),k2_mcart_1(k1_mcart_1(esk14_0))) = k1_mcart_1(esk14_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk14_0)),esk11_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk14_0)),esk10_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( esk8_1(esk14_0) = k2_mcart_1(esk14_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk14_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_44])).

cnf(c_0_74,negated_conjecture,
    ( esk13_0 != k7_mcart_1(esk10_0,esk11_0,esk12_0,esk14_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_75,negated_conjecture,
    ( k7_mcart_1(esk10_0,esk11_0,esk12_0,esk14_0) = k2_mcart_1(esk14_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_32]),c_0_26]),c_0_22]),c_0_16])).

cnf(c_0_76,negated_conjecture,
    ( esk13_0 = X1
    | k4_tarski(k1_mcart_1(esk14_0),X1) != esk14_0
    | ~ m1_subset_1(X1,esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])])).

cnf(c_0_77,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk14_0),k2_mcart_1(esk14_0)) = esk14_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk14_0),esk12_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k2_mcart_1(esk14_0) != esk13_0 ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 10.77/10.94  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 10.77/10.94  # and selection function SelectNegativeLiterals.
% 10.77/10.94  #
% 10.77/10.94  # Preprocessing time       : 0.029 s
% 10.77/10.94  # Presaturation interreduction done
% 10.77/10.94  
% 10.77/10.94  # Proof found!
% 10.77/10.94  # SZS status Theorem
% 10.77/10.94  # SZS output start CNFRefutation
% 10.77/10.94  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 10.77/10.94  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 10.77/10.94  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 10.77/10.94  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 10.77/10.94  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.77/10.94  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.77/10.94  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 10.77/10.94  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 10.77/10.94  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 10.77/10.94  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 10.77/10.94  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 10.77/10.94  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 10.77/10.94  fof(c_0_12, plain, ![X13, X14, X15, X16, X19, X20, X21, X22, X23, X24, X26, X27]:(((((r2_hidden(esk2_4(X13,X14,X15,X16),X13)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14))&(r2_hidden(esk3_4(X13,X14,X15,X16),X14)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(X16=k4_tarski(esk2_4(X13,X14,X15,X16),esk3_4(X13,X14,X15,X16))|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(~r2_hidden(X20,X13)|~r2_hidden(X21,X14)|X19!=k4_tarski(X20,X21)|r2_hidden(X19,X15)|X15!=k2_zfmisc_1(X13,X14)))&((~r2_hidden(esk4_3(X22,X23,X24),X24)|(~r2_hidden(X26,X22)|~r2_hidden(X27,X23)|esk4_3(X22,X23,X24)!=k4_tarski(X26,X27))|X24=k2_zfmisc_1(X22,X23))&(((r2_hidden(esk5_3(X22,X23,X24),X22)|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))&(r2_hidden(esk6_3(X22,X23,X24),X23)|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23)))&(esk4_3(X22,X23,X24)=k4_tarski(esk5_3(X22,X23,X24),esk6_3(X22,X23,X24))|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 10.77/10.94  fof(c_0_13, negated_conjecture, ![X77, X78, X79]:(m1_subset_1(esk14_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))&((~m1_subset_1(X77,esk10_0)|(~m1_subset_1(X78,esk11_0)|(~m1_subset_1(X79,esk12_0)|(esk14_0!=k3_mcart_1(X77,X78,X79)|esk13_0=X79))))&(((esk10_0!=k1_xboole_0&esk11_0!=k1_xboole_0)&esk12_0!=k1_xboole_0)&esk13_0!=k7_mcart_1(esk10_0,esk11_0,esk12_0,esk14_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 10.77/10.94  fof(c_0_14, plain, ![X56, X58, X59, X60, X61]:((r2_hidden(esk9_1(X56),X56)|X56=k1_xboole_0)&((~r2_hidden(X58,X56)|esk9_1(X56)!=k4_mcart_1(X58,X59,X60,X61)|X56=k1_xboole_0)&(~r2_hidden(X59,X56)|esk9_1(X56)!=k4_mcart_1(X58,X59,X60,X61)|X56=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 10.77/10.94  cnf(c_0_15, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 10.77/10.94  cnf(c_0_16, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.77/10.94  cnf(c_0_17, plain, (r2_hidden(esk9_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 10.77/10.94  fof(c_0_18, plain, ![X40, X41, X42]:k3_zfmisc_1(X40,X41,X42)=k2_zfmisc_1(k2_zfmisc_1(X40,X41),X42), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 10.77/10.94  fof(c_0_19, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 10.77/10.94  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).
% 10.77/10.94  cnf(c_0_21, negated_conjecture, (r2_hidden(esk9_1(esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 10.77/10.94  cnf(c_0_22, negated_conjecture, (esk11_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.77/10.94  fof(c_0_23, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 10.77/10.94  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk14_0,k3_zfmisc_1(esk10_0,esk11_0,esk12_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.77/10.94  cnf(c_0_25, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 10.77/10.94  cnf(c_0_26, negated_conjecture, (esk12_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.77/10.94  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.77/10.94  cnf(c_0_28, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 10.77/10.94  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk9_1(esk10_0),X1),k2_zfmisc_1(esk10_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 10.77/10.94  cnf(c_0_30, negated_conjecture, (r2_hidden(esk9_1(esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 10.77/10.94  cnf(c_0_31, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 10.77/10.94  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 10.77/10.94  cnf(c_0_33, negated_conjecture, (r2_hidden(esk9_1(esk12_0),esk12_0)), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 10.77/10.94  cnf(c_0_34, plain, (r2_hidden(esk1_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 10.77/10.94  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(esk9_1(esk10_0),esk9_1(esk11_0)),k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 10.77/10.94  cnf(c_0_36, negated_conjecture, (r2_hidden(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 10.77/10.94  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(X1,esk9_1(esk12_0)),k2_zfmisc_1(X2,esk12_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_33])).
% 10.77/10.94  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_1(k2_zfmisc_1(esk10_0,esk11_0)),k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 10.77/10.94  fof(c_0_39, plain, ![X47, X48, X49]:((r2_hidden(k1_mcart_1(X47),X48)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))&(r2_hidden(k2_mcart_1(X47),X49)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 10.77/10.94  cnf(c_0_40, negated_conjecture, (r2_hidden(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))), inference(spm,[status(thm)],[c_0_27, c_0_36])).
% 10.77/10.94  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk1_1(k2_zfmisc_1(esk10_0,esk11_0)),esk9_1(esk12_0)),k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 10.77/10.94  fof(c_0_42, plain, ![X30, X31, X32]:(~r2_hidden(X30,k2_zfmisc_1(X31,X32))|k4_tarski(esk7_1(X30),esk8_1(X30))=X30), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 10.77/10.94  cnf(c_0_43, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 10.77/10.94  cnf(c_0_44, negated_conjecture, (r2_hidden(esk14_0,k2_zfmisc_1(k2_zfmisc_1(esk10_0,esk11_0),esk12_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 10.77/10.94  fof(c_0_45, plain, ![X70, X71]:(k1_mcart_1(k4_tarski(X70,X71))=X70&k2_mcart_1(k4_tarski(X70,X71))=X71), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 10.77/10.94  cnf(c_0_46, plain, (k4_tarski(esk7_1(X1),esk8_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 10.77/10.94  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_mcart_1(esk14_0),k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 10.77/10.94  cnf(c_0_48, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 10.77/10.94  cnf(c_0_49, negated_conjecture, (k4_tarski(esk7_1(k1_mcart_1(esk14_0)),esk8_1(k1_mcart_1(esk14_0)))=k1_mcart_1(esk14_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 10.77/10.94  cnf(c_0_50, negated_conjecture, (esk7_1(k1_mcart_1(esk14_0))=k1_mcart_1(k1_mcart_1(esk14_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 10.77/10.94  cnf(c_0_51, negated_conjecture, (k4_tarski(esk7_1(esk14_0),esk8_1(esk14_0))=esk14_0), inference(spm,[status(thm)],[c_0_46, c_0_44])).
% 10.77/10.94  fof(c_0_52, plain, ![X62, X63, X64, X65]:(((k5_mcart_1(X62,X63,X64,X65)=k1_mcart_1(k1_mcart_1(X65))|~m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))|(X62=k1_xboole_0|X63=k1_xboole_0|X64=k1_xboole_0))&(k6_mcart_1(X62,X63,X64,X65)=k2_mcart_1(k1_mcart_1(X65))|~m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))|(X62=k1_xboole_0|X63=k1_xboole_0|X64=k1_xboole_0)))&(k7_mcart_1(X62,X63,X64,X65)=k2_mcart_1(X65)|~m1_subset_1(X65,k3_zfmisc_1(X62,X63,X64))|(X62=k1_xboole_0|X63=k1_xboole_0|X64=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 10.77/10.94  fof(c_0_53, plain, ![X37, X38, X39]:k3_mcart_1(X37,X38,X39)=k4_tarski(k4_tarski(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 10.77/10.94  cnf(c_0_54, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_45])).
% 10.77/10.94  cnf(c_0_55, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk14_0)),esk8_1(k1_mcart_1(esk14_0)))=k1_mcart_1(esk14_0)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 10.77/10.94  cnf(c_0_56, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 10.77/10.94  cnf(c_0_57, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 10.77/10.94  cnf(c_0_58, negated_conjecture, (esk7_1(esk14_0)=k1_mcart_1(esk14_0)), inference(spm,[status(thm)],[c_0_48, c_0_51])).
% 10.77/10.94  cnf(c_0_59, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 10.77/10.94  cnf(c_0_60, negated_conjecture, (esk13_0=X3|~m1_subset_1(X1,esk10_0)|~m1_subset_1(X2,esk11_0)|~m1_subset_1(X3,esk12_0)|esk14_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.77/10.94  cnf(c_0_61, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 10.77/10.94  cnf(c_0_62, negated_conjecture, (esk8_1(k1_mcart_1(esk14_0))=k2_mcart_1(k1_mcart_1(esk14_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 10.77/10.94  cnf(c_0_63, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_56, c_0_27])).
% 10.77/10.94  cnf(c_0_64, negated_conjecture, (r2_hidden(k2_mcart_1(k1_mcart_1(esk14_0)),esk11_0)), inference(spm,[status(thm)],[c_0_57, c_0_47])).
% 10.77/10.94  cnf(c_0_65, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk14_0)),esk10_0)), inference(spm,[status(thm)],[c_0_43, c_0_47])).
% 10.77/10.94  cnf(c_0_66, negated_conjecture, (k4_tarski(k1_mcart_1(esk14_0),esk8_1(esk14_0))=esk14_0), inference(rw,[status(thm)],[c_0_51, c_0_58])).
% 10.77/10.94  cnf(c_0_67, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_59, c_0_25])).
% 10.77/10.94  cnf(c_0_68, negated_conjecture, (esk13_0=X3|esk14_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk12_0)|~m1_subset_1(X2,esk11_0)|~m1_subset_1(X1,esk10_0)), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 10.77/10.94  cnf(c_0_69, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk14_0)),k2_mcart_1(k1_mcart_1(esk14_0)))=k1_mcart_1(esk14_0)), inference(rw,[status(thm)],[c_0_55, c_0_62])).
% 10.77/10.94  cnf(c_0_70, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk14_0)),esk11_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 10.77/10.94  cnf(c_0_71, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk14_0)),esk10_0)), inference(spm,[status(thm)],[c_0_63, c_0_65])).
% 10.77/10.94  cnf(c_0_72, negated_conjecture, (esk8_1(esk14_0)=k2_mcart_1(esk14_0)), inference(spm,[status(thm)],[c_0_54, c_0_66])).
% 10.77/10.94  cnf(c_0_73, negated_conjecture, (r2_hidden(k2_mcart_1(esk14_0),esk12_0)), inference(spm,[status(thm)],[c_0_57, c_0_44])).
% 10.77/10.94  cnf(c_0_74, negated_conjecture, (esk13_0!=k7_mcart_1(esk10_0,esk11_0,esk12_0,esk14_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 10.77/10.94  cnf(c_0_75, negated_conjecture, (k7_mcart_1(esk10_0,esk11_0,esk12_0,esk14_0)=k2_mcart_1(esk14_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_32]), c_0_26]), c_0_22]), c_0_16])).
% 10.77/10.94  cnf(c_0_76, negated_conjecture, (esk13_0=X1|k4_tarski(k1_mcart_1(esk14_0),X1)!=esk14_0|~m1_subset_1(X1,esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])])).
% 10.77/10.94  cnf(c_0_77, negated_conjecture, (k4_tarski(k1_mcart_1(esk14_0),k2_mcart_1(esk14_0))=esk14_0), inference(rw,[status(thm)],[c_0_66, c_0_72])).
% 10.77/10.94  cnf(c_0_78, negated_conjecture, (m1_subset_1(k2_mcart_1(esk14_0),esk12_0)), inference(spm,[status(thm)],[c_0_63, c_0_73])).
% 10.77/10.94  cnf(c_0_79, negated_conjecture, (k2_mcart_1(esk14_0)!=esk13_0), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 10.77/10.94  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])]), c_0_79]), ['proof']).
% 10.77/10.94  # SZS output end CNFRefutation
% 10.77/10.94  # Proof object total steps             : 81
% 10.77/10.94  # Proof object clause steps            : 58
% 10.77/10.94  # Proof object formula steps           : 23
% 10.77/10.94  # Proof object conjectures             : 43
% 10.77/10.94  # Proof object clause conjectures      : 40
% 10.77/10.94  # Proof object formula conjectures     : 3
% 10.77/10.94  # Proof object initial clauses used    : 20
% 10.77/10.94  # Proof object initial formulas used   : 11
% 10.77/10.94  # Proof object generating inferences   : 28
% 10.77/10.94  # Proof object simplifying inferences  : 20
% 10.77/10.94  # Training examples: 0 positive, 0 negative
% 10.77/10.94  # Parsed axioms                        : 15
% 10.77/10.94  # Removed by relevancy pruning/SinE    : 0
% 10.77/10.94  # Initial clauses                      : 42
% 10.77/10.94  # Removed in clause preprocessing      : 3
% 10.77/10.94  # Initial clauses in saturation        : 39
% 10.77/10.94  # Processed clauses                    : 8785
% 10.77/10.94  # ...of these trivial                  : 1060
% 10.77/10.94  # ...subsumed                          : 3805
% 10.77/10.94  # ...remaining for further processing  : 3920
% 10.77/10.94  # Other redundant clauses eliminated   : 9808
% 10.77/10.94  # Clauses deleted for lack of memory   : 0
% 10.77/10.94  # Backward-subsumed                    : 163
% 10.77/10.94  # Backward-rewritten                   : 181
% 10.77/10.94  # Generated clauses                    : 1891216
% 10.77/10.94  # ...of the previous two non-trivial   : 1641045
% 10.77/10.94  # Contextual simplify-reflections      : 19
% 10.77/10.94  # Paramodulations                      : 1881012
% 10.77/10.94  # Factorizations                       : 397
% 10.77/10.94  # Equation resolutions                 : 9808
% 10.77/10.94  # Propositional unsat checks           : 0
% 10.77/10.94  #    Propositional check models        : 0
% 10.77/10.94  #    Propositional check unsatisfiable : 0
% 10.77/10.94  #    Propositional clauses             : 0
% 10.77/10.94  #    Propositional clauses after purity: 0
% 10.77/10.94  #    Propositional unsat core size     : 0
% 10.77/10.94  #    Propositional preprocessing time  : 0.000
% 10.77/10.94  #    Propositional encoding time       : 0.000
% 10.77/10.94  #    Propositional solver time         : 0.000
% 10.77/10.94  #    Success case prop preproc time    : 0.000
% 10.77/10.94  #    Success case prop encoding time   : 0.000
% 10.77/10.94  #    Success case prop solver time     : 0.000
% 10.77/10.94  # Current number of processed clauses  : 3527
% 10.77/10.94  #    Positive orientable unit clauses  : 1288
% 10.77/10.94  #    Positive unorientable unit clauses: 0
% 10.77/10.94  #    Negative unit clauses             : 16
% 10.77/10.94  #    Non-unit-clauses                  : 2223
% 10.77/10.94  # Current number of unprocessed clauses: 1628365
% 10.77/10.94  # ...number of literals in the above   : 6053489
% 10.77/10.94  # Current number of archived formulas  : 0
% 10.77/10.94  # Current number of archived clauses   : 386
% 10.77/10.94  # Clause-clause subsumption calls (NU) : 454889
% 10.77/10.94  # Rec. Clause-clause subsumption calls : 307401
% 10.77/10.94  # Non-unit clause-clause subsumptions  : 3958
% 10.77/10.94  # Unit Clause-clause subsumption calls : 95795
% 10.77/10.94  # Rewrite failures with RHS unbound    : 0
% 10.77/10.94  # BW rewrite match attempts            : 2869
% 10.77/10.94  # BW rewrite match successes           : 46
% 10.77/10.94  # Condensation attempts                : 0
% 10.77/10.94  # Condensation successes               : 0
% 10.77/10.94  # Termbank termtop insertions          : 37458813
% 10.80/10.99  
% 10.80/10.99  # -------------------------------------------------
% 10.80/10.99  # User time                : 10.049 s
% 10.80/10.99  # System time              : 0.580 s
% 10.80/10.99  # Total time               : 10.629 s
% 10.80/10.99  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
