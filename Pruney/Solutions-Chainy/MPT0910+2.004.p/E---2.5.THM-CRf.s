%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:11 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  101 (4151 expanded)
%              Number of clauses        :   66 (2090 expanded)
%              Number of leaves         :   17 (1003 expanded)
%              Depth                    :   19
%              Number of atoms          :  269 (11839 expanded)
%              Number of equality atoms :  150 (10615 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t70_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X1)
           => ! [X7] :
                ( m1_subset_1(X7,X2)
               => ! [X8] :
                    ( m1_subset_1(X8,X3)
                   => ( X5 = k3_mcart_1(X6,X7,X8)
                     => X4 = X7 ) ) ) )
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X3 = k1_xboole_0
          | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

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

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_17,plain,(
    ! [X40,X41,X42,X43] : k4_zfmisc_1(X40,X41,X42,X43) = k2_zfmisc_1(k3_zfmisc_1(X40,X41,X42),X43) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X37,X38,X39] : k3_zfmisc_1(X37,X38,X39) = k2_zfmisc_1(k2_zfmisc_1(X37,X38),X39) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_19,plain,(
    ! [X63,X64,X65,X66] :
      ( ( X63 = k1_xboole_0
        | X64 = k1_xboole_0
        | X65 = k1_xboole_0
        | X66 = k1_xboole_0
        | k4_zfmisc_1(X63,X64,X65,X66) != k1_xboole_0 )
      & ( X63 != k1_xboole_0
        | k4_zfmisc_1(X63,X64,X65,X66) = k1_xboole_0 )
      & ( X64 != k1_xboole_0
        | k4_zfmisc_1(X63,X64,X65,X66) = k1_xboole_0 )
      & ( X65 != k1_xboole_0
        | k4_zfmisc_1(X63,X64,X65,X66) = k1_xboole_0 )
      & ( X66 != k1_xboole_0
        | k4_zfmisc_1(X63,X64,X65,X66) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_20,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_27,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

fof(c_0_28,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X1)
             => ! [X7] :
                  ( m1_subset_1(X7,X2)
                 => ! [X8] :
                      ( m1_subset_1(X8,X3)
                     => ( X5 = k3_mcart_1(X6,X7,X8)
                       => X4 = X7 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_mcart_1])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X53,X55,X56,X57,X58] :
      ( ( r2_hidden(esk3_1(X53),X53)
        | X53 = k1_xboole_0 )
      & ( ~ r2_hidden(X55,X53)
        | esk3_1(X53) != k4_mcart_1(X55,X56,X57,X58)
        | X53 = k1_xboole_0 )
      & ( ~ r2_hidden(X56,X53)
        | esk3_1(X53) != k4_mcart_1(X55,X56,X57,X58)
        | X53 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

fof(c_0_33,negated_conjecture,(
    ! [X72,X73,X74] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X72,esk4_0)
        | ~ m1_subset_1(X73,esk5_0)
        | ~ m1_subset_1(X74,esk6_0)
        | esk8_0 != k3_mcart_1(X72,X73,X74)
        | esk7_0 = X73 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])])).

cnf(c_0_34,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_31]),c_0_32])).

fof(c_0_37,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r2_hidden(X25,X27)
        | k4_xboole_0(k2_tarski(X25,X26),X27) != k2_tarski(X25,X26) )
      & ( ~ r2_hidden(X26,X27)
        | k4_xboole_0(k2_tarski(X25,X26),X27) != k2_tarski(X25,X26) )
      & ( r2_hidden(X25,X27)
        | r2_hidden(X26,X27)
        | k4_xboole_0(k2_tarski(X25,X26),X27) = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_38,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_39,negated_conjecture,
    ( esk7_0 != k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_36])])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X13] : k4_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_44,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X3,X2)),k2_zfmisc_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

fof(c_0_45,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k4_xboole_0(k1_enumset1(X3,X3,X1),X2) != k1_enumset1(X3,X3,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_48,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_44]),c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_52,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_21])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,esk5_0)),k2_zfmisc_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_59,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(esk4_0,esk5_0)),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_63,plain,(
    ! [X59,X60,X61,X62] :
      ( ( k5_mcart_1(X59,X60,X61,X62) = k1_mcart_1(k1_mcart_1(X62))
        | ~ m1_subset_1(X62,k3_zfmisc_1(X59,X60,X61))
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0 )
      & ( k6_mcart_1(X59,X60,X61,X62) = k2_mcart_1(k1_mcart_1(X62))
        | ~ m1_subset_1(X62,k3_zfmisc_1(X59,X60,X61))
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0 )
      & ( k7_mcart_1(X59,X60,X61,X62) = k2_mcart_1(X62)
        | ~ m1_subset_1(X62,k3_zfmisc_1(X59,X60,X61))
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0
        | X61 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_64,plain,(
    ! [X48,X49,X50] :
      ( ( r2_hidden(k1_mcart_1(X48),X49)
        | ~ r2_hidden(X48,k2_zfmisc_1(X49,X50)) )
      & ( r2_hidden(k2_mcart_1(X48),X50)
        | ~ r2_hidden(X48,k2_zfmisc_1(X49,X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_68,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | ~ r2_hidden(X51,X52)
      | X51 = k4_tarski(k1_mcart_1(X51),k2_mcart_1(X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_69,plain,(
    ! [X32,X33] : v1_relat_1(k2_zfmisc_1(X32,X33)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_70,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_67,c_0_21])).

fof(c_0_73,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X47,k3_zfmisc_1(X44,X45,X46))
      | m1_subset_1(k7_mcart_1(X44,X45,X46,X47),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_74,plain,(
    ! [X34,X35,X36] : k3_mcart_1(X34,X35,X36) = k4_tarski(k4_tarski(X34,X35),X36) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_75,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_77,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_78,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk8_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_49]),c_0_51]),c_0_57])).

cnf(c_0_81,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_82,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_83,negated_conjecture,
    ( esk7_0 = X2
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_84,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_85,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_79])).

cnf(c_0_89,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_21])).

cnf(c_0_90,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_82,c_0_21])).

cnf(c_0_91,negated_conjecture,
    ( esk7_0 = X2
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk8_0)),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) = k1_mcart_1(esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_79]),c_0_80])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(esk8_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_54])).

cnf(c_0_96,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_54]),c_0_49]),c_0_51]),c_0_57])).

cnf(c_0_97,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),X1) != esk8_0
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_94])]),c_0_39])).

cnf(c_0_98,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_71])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.06/3.24  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 3.06/3.24  # and selection function SelectNegativeLiterals.
% 3.06/3.24  #
% 3.06/3.24  # Preprocessing time       : 0.029 s
% 3.06/3.24  # Presaturation interreduction done
% 3.06/3.24  
% 3.06/3.24  # Proof found!
% 3.06/3.24  # SZS status Theorem
% 3.06/3.24  # SZS output start CNFRefutation
% 3.06/3.24  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 3.06/3.24  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.06/3.24  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 3.06/3.24  fof(t70_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 3.06/3.24  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.06/3.24  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.06/3.24  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.06/3.24  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.06/3.24  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.06/3.24  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.06/3.24  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.06/3.24  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.06/3.24  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.06/3.24  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.06/3.24  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 3.06/3.24  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.06/3.24  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.06/3.24  fof(c_0_17, plain, ![X40, X41, X42, X43]:k4_zfmisc_1(X40,X41,X42,X43)=k2_zfmisc_1(k3_zfmisc_1(X40,X41,X42),X43), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 3.06/3.24  fof(c_0_18, plain, ![X37, X38, X39]:k3_zfmisc_1(X37,X38,X39)=k2_zfmisc_1(k2_zfmisc_1(X37,X38),X39), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 3.06/3.24  fof(c_0_19, plain, ![X63, X64, X65, X66]:((X63=k1_xboole_0|X64=k1_xboole_0|X65=k1_xboole_0|X66=k1_xboole_0|k4_zfmisc_1(X63,X64,X65,X66)!=k1_xboole_0)&((((X63!=k1_xboole_0|k4_zfmisc_1(X63,X64,X65,X66)=k1_xboole_0)&(X64!=k1_xboole_0|k4_zfmisc_1(X63,X64,X65,X66)=k1_xboole_0))&(X65!=k1_xboole_0|k4_zfmisc_1(X63,X64,X65,X66)=k1_xboole_0))&(X66!=k1_xboole_0|k4_zfmisc_1(X63,X64,X65,X66)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 3.06/3.24  cnf(c_0_20, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 3.06/3.24  cnf(c_0_21, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.06/3.24  cnf(c_0_22, plain, (k4_zfmisc_1(X2,X3,X4,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.06/3.24  cnf(c_0_23, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 3.06/3.24  cnf(c_0_24, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.06/3.24  cnf(c_0_25, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 3.06/3.24  cnf(c_0_26, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 3.06/3.24  cnf(c_0_27, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 3.06/3.24  fof(c_0_28, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t70_mcart_1])).
% 3.06/3.24  cnf(c_0_29, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.06/3.24  fof(c_0_30, plain, ![X53, X55, X56, X57, X58]:((r2_hidden(esk3_1(X53),X53)|X53=k1_xboole_0)&((~r2_hidden(X55,X53)|esk3_1(X53)!=k4_mcart_1(X55,X56,X57,X58)|X53=k1_xboole_0)&(~r2_hidden(X56,X53)|esk3_1(X53)!=k4_mcart_1(X55,X56,X57,X58)|X53=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 3.06/3.24  cnf(c_0_31, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_26])).
% 3.06/3.24  cnf(c_0_32, plain, (k2_zfmisc_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 3.06/3.24  fof(c_0_33, negated_conjecture, ![X72, X73, X74]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X72,esk4_0)|(~m1_subset_1(X73,esk5_0)|(~m1_subset_1(X74,esk6_0)|(esk8_0!=k3_mcart_1(X72,X73,X74)|esk7_0=X73))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])])).
% 3.06/3.24  cnf(c_0_34, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_23])).
% 3.06/3.24  cnf(c_0_35, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.06/3.24  cnf(c_0_36, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_31]), c_0_32])).
% 3.06/3.24  fof(c_0_37, plain, ![X25, X26, X27]:(((~r2_hidden(X25,X27)|k4_xboole_0(k2_tarski(X25,X26),X27)!=k2_tarski(X25,X26))&(~r2_hidden(X26,X27)|k4_xboole_0(k2_tarski(X25,X26),X27)!=k2_tarski(X25,X26)))&(r2_hidden(X25,X27)|r2_hidden(X26,X27)|k4_xboole_0(k2_tarski(X25,X26),X27)=k2_tarski(X25,X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 3.06/3.24  fof(c_0_38, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 3.06/3.24  cnf(c_0_39, negated_conjecture, (esk7_0!=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.06/3.24  cnf(c_0_40, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_36])])).
% 3.06/3.24  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 3.06/3.24  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 3.06/3.24  fof(c_0_43, plain, ![X13]:k4_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t3_boole])).
% 3.06/3.24  cnf(c_0_44, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X3,X2)),k2_zfmisc_1(X3,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_40])).
% 3.06/3.24  fof(c_0_45, plain, ![X30, X31]:(~m1_subset_1(X30,X31)|(v1_xboole_0(X31)|r2_hidden(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 3.06/3.24  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.06/3.24  cnf(c_0_47, plain, (k4_xboole_0(k1_enumset1(X3,X3,X1),X2)!=k1_enumset1(X3,X3,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 3.06/3.24  cnf(c_0_48, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.06/3.24  cnf(c_0_49, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.06/3.24  cnf(c_0_50, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_44]), c_0_44])).
% 3.06/3.24  cnf(c_0_51, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.06/3.24  fof(c_0_52, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 3.06/3.24  cnf(c_0_53, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 3.06/3.24  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_46, c_0_21])).
% 3.06/3.24  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 3.06/3.24  cnf(c_0_56, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 3.06/3.24  cnf(c_0_57, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.06/3.24  cnf(c_0_58, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,esk5_0)),k2_zfmisc_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 3.06/3.24  cnf(c_0_59, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 3.06/3.24  cnf(c_0_60, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 3.06/3.24  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 3.06/3.24  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(esk4_0,esk5_0)),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 3.06/3.24  fof(c_0_63, plain, ![X59, X60, X61, X62]:(((k5_mcart_1(X59,X60,X61,X62)=k1_mcart_1(k1_mcart_1(X62))|~m1_subset_1(X62,k3_zfmisc_1(X59,X60,X61))|(X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0))&(k6_mcart_1(X59,X60,X61,X62)=k2_mcart_1(k1_mcart_1(X62))|~m1_subset_1(X62,k3_zfmisc_1(X59,X60,X61))|(X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0)))&(k7_mcart_1(X59,X60,X61,X62)=k2_mcart_1(X62)|~m1_subset_1(X62,k3_zfmisc_1(X59,X60,X61))|(X59=k1_xboole_0|X60=k1_xboole_0|X61=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 3.06/3.24  fof(c_0_64, plain, ![X48, X49, X50]:((r2_hidden(k1_mcart_1(X48),X49)|~r2_hidden(X48,k2_zfmisc_1(X49,X50)))&(r2_hidden(k2_mcart_1(X48),X50)|~r2_hidden(X48,k2_zfmisc_1(X49,X50)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 3.06/3.24  cnf(c_0_65, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 3.06/3.24  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 3.06/3.24  cnf(c_0_67, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 3.06/3.24  fof(c_0_68, plain, ![X51, X52]:(~v1_relat_1(X52)|(~r2_hidden(X51,X52)|X51=k4_tarski(k1_mcart_1(X51),k2_mcart_1(X51)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 3.06/3.24  fof(c_0_69, plain, ![X32, X33]:v1_relat_1(k2_zfmisc_1(X32,X33)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 3.06/3.24  cnf(c_0_70, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 3.06/3.24  cnf(c_0_71, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 3.06/3.24  cnf(c_0_72, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_67, c_0_21])).
% 3.06/3.24  fof(c_0_73, plain, ![X44, X45, X46, X47]:(~m1_subset_1(X47,k3_zfmisc_1(X44,X45,X46))|m1_subset_1(k7_mcart_1(X44,X45,X46,X47),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 3.06/3.24  fof(c_0_74, plain, ![X34, X35, X36]:k3_mcart_1(X34,X35,X36)=k4_tarski(k4_tarski(X34,X35),X36), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 3.06/3.24  cnf(c_0_75, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 3.06/3.24  cnf(c_0_76, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 3.06/3.24  fof(c_0_77, plain, ![X28, X29]:(~r2_hidden(X28,X29)|m1_subset_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 3.06/3.24  cnf(c_0_78, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 3.06/3.24  cnf(c_0_79, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 3.06/3.24  cnf(c_0_80, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk8_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_54]), c_0_49]), c_0_51]), c_0_57])).
% 3.06/3.24  cnf(c_0_81, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 3.06/3.24  cnf(c_0_82, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 3.06/3.24  cnf(c_0_83, negated_conjecture, (esk7_0=X2|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 3.06/3.24  cnf(c_0_84, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 3.06/3.24  cnf(c_0_85, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 3.06/3.24  cnf(c_0_86, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 3.06/3.24  cnf(c_0_87, negated_conjecture, (r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 3.06/3.24  cnf(c_0_88, negated_conjecture, (r2_hidden(k1_mcart_1(k1_mcart_1(esk8_0)),esk4_0)), inference(spm,[status(thm)],[c_0_70, c_0_79])).
% 3.06/3.24  cnf(c_0_89, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_81, c_0_21])).
% 3.06/3.24  cnf(c_0_90, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_82, c_0_21])).
% 3.06/3.24  cnf(c_0_91, negated_conjecture, (esk7_0=X2|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_83, c_0_84])).
% 3.06/3.24  cnf(c_0_92, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk8_0)),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))=k1_mcart_1(esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_79]), c_0_80])).
% 3.06/3.24  cnf(c_0_93, negated_conjecture, (m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 3.06/3.24  cnf(c_0_94, negated_conjecture, (m1_subset_1(k1_mcart_1(k1_mcart_1(esk8_0)),esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_88])).
% 3.06/3.24  cnf(c_0_95, negated_conjecture, (m1_subset_1(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_89, c_0_54])).
% 3.06/3.24  cnf(c_0_96, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_54]), c_0_49]), c_0_51]), c_0_57])).
% 3.06/3.24  cnf(c_0_97, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),X1)!=esk8_0|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_94])]), c_0_39])).
% 3.06/3.24  cnf(c_0_98, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_85, c_0_71])).
% 3.06/3.24  cnf(c_0_99, negated_conjecture, (m1_subset_1(k2_mcart_1(esk8_0),esk6_0)), inference(rw,[status(thm)],[c_0_95, c_0_96])).
% 3.06/3.24  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])]), ['proof']).
% 3.06/3.24  # SZS output end CNFRefutation
% 3.06/3.24  # Proof object total steps             : 101
% 3.06/3.24  # Proof object clause steps            : 66
% 3.06/3.24  # Proof object formula steps           : 35
% 3.06/3.24  # Proof object conjectures             : 34
% 3.06/3.24  # Proof object clause conjectures      : 31
% 3.06/3.24  # Proof object formula conjectures     : 3
% 3.06/3.24  # Proof object initial clauses used    : 26
% 3.06/3.24  # Proof object initial formulas used   : 17
% 3.06/3.24  # Proof object generating inferences   : 27
% 3.06/3.24  # Proof object simplifying inferences  : 34
% 3.06/3.24  # Training examples: 0 positive, 0 negative
% 3.06/3.24  # Parsed axioms                        : 18
% 3.06/3.24  # Removed by relevancy pruning/SinE    : 0
% 3.06/3.24  # Initial clauses                      : 40
% 3.06/3.24  # Removed in clause preprocessing      : 4
% 3.06/3.24  # Initial clauses in saturation        : 36
% 3.06/3.24  # Processed clauses                    : 6846
% 3.06/3.24  # ...of these trivial                  : 1260
% 3.06/3.24  # ...subsumed                          : 4456
% 3.06/3.24  # ...remaining for further processing  : 1130
% 3.06/3.24  # Other redundant clauses eliminated   : 1329
% 3.06/3.24  # Clauses deleted for lack of memory   : 0
% 3.06/3.24  # Backward-subsumed                    : 25
% 3.06/3.24  # Backward-rewritten                   : 73
% 3.06/3.24  # Generated clauses                    : 246409
% 3.06/3.24  # ...of the previous two non-trivial   : 174653
% 3.06/3.24  # Contextual simplify-reflections      : 14
% 3.06/3.24  # Paramodulations                      : 244585
% 3.06/3.24  # Factorizations                       : 495
% 3.06/3.24  # Equation resolutions                 : 1331
% 3.06/3.24  # Propositional unsat checks           : 0
% 3.06/3.24  #    Propositional check models        : 0
% 3.06/3.24  #    Propositional check unsatisfiable : 0
% 3.06/3.24  #    Propositional clauses             : 0
% 3.06/3.24  #    Propositional clauses after purity: 0
% 3.06/3.24  #    Propositional unsat core size     : 0
% 3.06/3.24  #    Propositional preprocessing time  : 0.000
% 3.06/3.24  #    Propositional encoding time       : 0.000
% 3.06/3.24  #    Propositional solver time         : 0.000
% 3.06/3.24  #    Success case prop preproc time    : 0.000
% 3.06/3.24  #    Success case prop encoding time   : 0.000
% 3.06/3.24  #    Success case prop solver time     : 0.000
% 3.06/3.24  # Current number of processed clauses  : 989
% 3.06/3.24  #    Positive orientable unit clauses  : 527
% 3.06/3.24  #    Positive unorientable unit clauses: 0
% 3.06/3.24  #    Negative unit clauses             : 5
% 3.06/3.24  #    Non-unit-clauses                  : 457
% 3.06/3.24  # Current number of unprocessed clauses: 166223
% 3.06/3.24  # ...number of literals in the above   : 823077
% 3.06/3.24  # Current number of archived formulas  : 0
% 3.06/3.24  # Current number of archived clauses   : 138
% 3.06/3.24  # Clause-clause subsumption calls (NU) : 77123
% 3.06/3.24  # Rec. Clause-clause subsumption calls : 51976
% 3.06/3.24  # Non-unit clause-clause subsumptions  : 4431
% 3.06/3.24  # Unit Clause-clause subsumption calls : 3731
% 3.06/3.24  # Rewrite failures with RHS unbound    : 0
% 3.06/3.24  # BW rewrite match attempts            : 1831
% 3.06/3.24  # BW rewrite match successes           : 27
% 3.06/3.24  # Condensation attempts                : 0
% 3.06/3.24  # Condensation successes               : 0
% 3.06/3.24  # Termbank termtop insertions          : 4036199
% 3.06/3.25  
% 3.06/3.25  # -------------------------------------------------
% 3.06/3.25  # User time                : 2.807 s
% 3.06/3.25  # System time              : 0.095 s
% 3.06/3.25  # Total time               : 2.902 s
% 3.06/3.25  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
