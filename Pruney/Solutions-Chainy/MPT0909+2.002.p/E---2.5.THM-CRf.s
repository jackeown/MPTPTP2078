%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:08 EST 2020

% Result     : Theorem 0.78s
% Output     : CNFRefutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  100 (4179 expanded)
%              Number of clauses        :   67 (2098 expanded)
%              Number of leaves         :   16 (1009 expanded)
%              Depth                    :   19
%              Number of atoms          :  269 (12111 expanded)
%              Number of equality atoms :  147 (10771 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

fof(c_0_16,plain,(
    ! [X39,X40,X41,X42] : k4_zfmisc_1(X39,X40,X41,X42) = k2_zfmisc_1(k3_zfmisc_1(X39,X40,X41),X42) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X36,X37,X38] : k3_zfmisc_1(X36,X37,X38) = k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X62,X63,X64,X65] :
      ( ( X62 = k1_xboole_0
        | X63 = k1_xboole_0
        | X64 = k1_xboole_0
        | X65 = k1_xboole_0
        | k4_zfmisc_1(X62,X63,X64,X65) != k1_xboole_0 )
      & ( X62 != k1_xboole_0
        | k4_zfmisc_1(X62,X63,X64,X65) = k1_xboole_0 )
      & ( X63 != k1_xboole_0
        | k4_zfmisc_1(X62,X63,X64,X65) = k1_xboole_0 )
      & ( X64 != k1_xboole_0
        | k4_zfmisc_1(X62,X63,X64,X65) = k1_xboole_0 )
      & ( X65 != k1_xboole_0
        | k4_zfmisc_1(X62,X63,X64,X65) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_19,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_27,negated_conjecture,(
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

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X52,X54,X55,X56,X57] :
      ( ( r2_hidden(esk3_1(X52),X52)
        | X52 = k1_xboole_0 )
      & ( ~ r2_hidden(X54,X52)
        | esk3_1(X52) != k4_mcart_1(X54,X55,X56,X57)
        | X52 = k1_xboole_0 )
      & ( ~ r2_hidden(X55,X52)
        | esk3_1(X52) != k4_mcart_1(X54,X55,X56,X57)
        | X52 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

fof(c_0_32,negated_conjecture,(
    ! [X71,X72,X73] :
      ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X71,esk4_0)
        | ~ m1_subset_1(X72,esk5_0)
        | ~ m1_subset_1(X73,esk6_0)
        | esk8_0 != k3_mcart_1(X71,X72,X73)
        | esk7_0 = X71 )
      & esk4_0 != k1_xboole_0
      & esk5_0 != k1_xboole_0
      & esk6_0 != k1_xboole_0
      & esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).

cnf(c_0_33,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_30]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( esk7_0 != k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_35])])).

fof(c_0_38,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_39,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X3,X2)),k2_zfmisc_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

fof(c_0_41,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_40]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_48,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_54,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(k2_zfmisc_1(X1,esk5_0)),k2_zfmisc_1(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_55,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(esk4_0,esk5_0)),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_59,plain,(
    ! [X58,X59,X60,X61] :
      ( ( k5_mcart_1(X58,X59,X60,X61) = k1_mcart_1(k1_mcart_1(X61))
        | ~ m1_subset_1(X61,k3_zfmisc_1(X58,X59,X60))
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0 )
      & ( k6_mcart_1(X58,X59,X60,X61) = k2_mcart_1(k1_mcart_1(X61))
        | ~ m1_subset_1(X61,k3_zfmisc_1(X58,X59,X60))
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0 )
      & ( k7_mcart_1(X58,X59,X60,X61) = k2_mcart_1(X61)
        | ~ m1_subset_1(X61,k3_zfmisc_1(X58,X59,X60))
        | X58 = k1_xboole_0
        | X59 = k1_xboole_0
        | X60 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_60,plain,(
    ! [X47,X48,X49] :
      ( ( r2_hidden(k1_mcart_1(X47),X48)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) )
      & ( r2_hidden(k2_mcart_1(X47),X49)
        | ~ r2_hidden(X47,k2_zfmisc_1(X48,X49)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_65,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X51)
      | ~ r2_hidden(X50,X51)
      | X50 = k4_tarski(k1_mcart_1(X50),k2_mcart_1(X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_66,plain,(
    ! [X29,X30] : v1_relat_1(k2_zfmisc_1(X29,X30)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_67,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_20])).

cnf(c_0_70,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_20])).

fof(c_0_71,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
      | m1_subset_1(k7_mcart_1(X43,X44,X45,X46),X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_72,plain,(
    ! [X33,X34,X35] : k3_mcart_1(X33,X34,X35) = k4_tarski(k4_tarski(X33,X34),X35) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_73,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_75,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | m1_subset_1(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_76,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk8_0)) = k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_50]),c_0_45]),c_0_47]),c_0_53])).

cnf(c_0_79,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk8_0)) = k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_50]),c_0_45]),c_0_47]),c_0_53])).

cnf(c_0_80,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_81,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_82,negated_conjecture,
    ( esk7_0 = X1
    | ~ m1_subset_1(X1,esk4_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X3,esk6_0)
    | esk8_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_83,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_84,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_77]),c_0_79])).

cnf(c_0_88,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_80,c_0_20])).

cnf(c_0_89,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_20])).

cnf(c_0_90,negated_conjecture,
    ( esk7_0 = X1
    | esk8_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk6_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)) = k1_mcart_1(esk8_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_77]),c_0_79]),c_0_78])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_50])).

cnf(c_0_95,negated_conjecture,
    ( k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0) = k2_mcart_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_50]),c_0_45]),c_0_47]),c_0_53])).

cnf(c_0_96,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),X1) != esk8_0
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_93])]),c_0_36])).

cnf(c_0_97,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_68])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk8_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:04:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.20/0.34  # No SInE strategy applied
% 0.20/0.34  # Trying AutoSched0 for 299 seconds
% 0.78/0.93  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.78/0.93  # and selection function SelectNegativeLiterals.
% 0.78/0.93  #
% 0.78/0.93  # Preprocessing time       : 0.028 s
% 0.78/0.93  # Presaturation interreduction done
% 0.78/0.93  
% 0.78/0.93  # Proof found!
% 0.78/0.93  # SZS status Theorem
% 0.78/0.93  # SZS output start CNFRefutation
% 0.78/0.93  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.78/0.93  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.78/0.93  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.78/0.93  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 0.78/0.93  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.78/0.93  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.78/0.93  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.78/0.93  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.78/0.93  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.78/0.93  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.78/0.93  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.78/0.93  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 0.78/0.93  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.78/0.93  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 0.78/0.93  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.78/0.93  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.78/0.93  fof(c_0_16, plain, ![X39, X40, X41, X42]:k4_zfmisc_1(X39,X40,X41,X42)=k2_zfmisc_1(k3_zfmisc_1(X39,X40,X41),X42), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.78/0.93  fof(c_0_17, plain, ![X36, X37, X38]:k3_zfmisc_1(X36,X37,X38)=k2_zfmisc_1(k2_zfmisc_1(X36,X37),X38), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.78/0.93  fof(c_0_18, plain, ![X62, X63, X64, X65]:((X62=k1_xboole_0|X63=k1_xboole_0|X64=k1_xboole_0|X65=k1_xboole_0|k4_zfmisc_1(X62,X63,X64,X65)!=k1_xboole_0)&((((X62!=k1_xboole_0|k4_zfmisc_1(X62,X63,X64,X65)=k1_xboole_0)&(X63!=k1_xboole_0|k4_zfmisc_1(X62,X63,X64,X65)=k1_xboole_0))&(X64!=k1_xboole_0|k4_zfmisc_1(X62,X63,X64,X65)=k1_xboole_0))&(X65!=k1_xboole_0|k4_zfmisc_1(X62,X63,X64,X65)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.78/0.93  cnf(c_0_19, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.78/0.93  cnf(c_0_20, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.78/0.93  cnf(c_0_21, plain, (k4_zfmisc_1(X2,X3,X4,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.93  cnf(c_0_22, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.78/0.93  cnf(c_0_23, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.93  cnf(c_0_24, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.78/0.93  cnf(c_0_25, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 0.78/0.93  cnf(c_0_26, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_24])).
% 0.78/0.93  fof(c_0_27, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 0.78/0.93  cnf(c_0_28, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.78/0.93  fof(c_0_29, plain, ![X52, X54, X55, X56, X57]:((r2_hidden(esk3_1(X52),X52)|X52=k1_xboole_0)&((~r2_hidden(X54,X52)|esk3_1(X52)!=k4_mcart_1(X54,X55,X56,X57)|X52=k1_xboole_0)&(~r2_hidden(X55,X52)|esk3_1(X52)!=k4_mcart_1(X54,X55,X56,X57)|X52=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.78/0.93  cnf(c_0_30, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_25])).
% 0.78/0.93  cnf(c_0_31, plain, (k2_zfmisc_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_26, c_0_26])).
% 0.78/0.93  fof(c_0_32, negated_conjecture, ![X71, X72, X73]:(m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))&((~m1_subset_1(X71,esk4_0)|(~m1_subset_1(X72,esk5_0)|(~m1_subset_1(X73,esk6_0)|(esk8_0!=k3_mcart_1(X71,X72,X73)|esk7_0=X71))))&(((esk4_0!=k1_xboole_0&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0)&esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])])).
% 0.78/0.93  cnf(c_0_33, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_28, c_0_22])).
% 0.78/0.93  cnf(c_0_34, plain, (r2_hidden(esk3_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.78/0.93  cnf(c_0_35, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_30]), c_0_31])).
% 0.78/0.93  cnf(c_0_36, negated_conjecture, (esk7_0!=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.78/0.93  cnf(c_0_37, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_35])])).
% 0.78/0.93  fof(c_0_38, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.78/0.93  fof(c_0_39, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.78/0.93  cnf(c_0_40, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X3,X2)),k2_zfmisc_1(X3,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 0.78/0.93  fof(c_0_41, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.78/0.93  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk8_0,k3_zfmisc_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.78/0.93  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.78/0.93  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.78/0.93  cnf(c_0_45, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.78/0.93  cnf(c_0_46, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_40]), c_0_40])).
% 0.78/0.93  cnf(c_0_47, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.78/0.93  fof(c_0_48, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.78/0.93  cnf(c_0_49, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.78/0.93  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(rw,[status(thm)],[c_0_42, c_0_20])).
% 0.78/0.93  cnf(c_0_51, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.78/0.93  cnf(c_0_52, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.78/0.93  cnf(c_0_53, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.78/0.93  cnf(c_0_54, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_1(k2_zfmisc_1(X1,esk5_0)),k2_zfmisc_1(X1,esk5_0))), inference(spm,[status(thm)],[c_0_47, c_0_46])).
% 0.78/0.93  cnf(c_0_55, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.78/0.93  cnf(c_0_56, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.78/0.93  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(X1,esk6_0)),k2_zfmisc_1(X1,esk6_0))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.78/0.93  cnf(c_0_58, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(esk4_0,esk5_0)),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.78/0.93  fof(c_0_59, plain, ![X58, X59, X60, X61]:(((k5_mcart_1(X58,X59,X60,X61)=k1_mcart_1(k1_mcart_1(X61))|~m1_subset_1(X61,k3_zfmisc_1(X58,X59,X60))|(X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0))&(k6_mcart_1(X58,X59,X60,X61)=k2_mcart_1(k1_mcart_1(X61))|~m1_subset_1(X61,k3_zfmisc_1(X58,X59,X60))|(X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0)))&(k7_mcart_1(X58,X59,X60,X61)=k2_mcart_1(X61)|~m1_subset_1(X61,k3_zfmisc_1(X58,X59,X60))|(X58=k1_xboole_0|X59=k1_xboole_0|X60=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.78/0.93  fof(c_0_60, plain, ![X47, X48, X49]:((r2_hidden(k1_mcart_1(X47),X48)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))&(r2_hidden(k2_mcart_1(X47),X49)|~r2_hidden(X47,k2_zfmisc_1(X48,X49)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.78/0.93  cnf(c_0_61, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.78/0.93  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_1(k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)),k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.78/0.93  cnf(c_0_63, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.78/0.93  cnf(c_0_64, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.78/0.93  fof(c_0_65, plain, ![X50, X51]:(~v1_relat_1(X51)|(~r2_hidden(X50,X51)|X50=k4_tarski(k1_mcart_1(X50),k2_mcart_1(X50)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 0.78/0.93  fof(c_0_66, plain, ![X29, X30]:v1_relat_1(k2_zfmisc_1(X29,X30)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.78/0.93  cnf(c_0_67, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.78/0.93  cnf(c_0_68, negated_conjecture, (r2_hidden(esk8_0,k2_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0),esk6_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.78/0.93  cnf(c_0_69, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_63, c_0_20])).
% 0.78/0.93  cnf(c_0_70, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_64, c_0_20])).
% 0.78/0.93  fof(c_0_71, plain, ![X43, X44, X45, X46]:(~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|m1_subset_1(k7_mcart_1(X43,X44,X45,X46),X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 0.78/0.93  fof(c_0_72, plain, ![X33, X34, X35]:k3_mcart_1(X33,X34,X35)=k4_tarski(k4_tarski(X33,X34),X35), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.78/0.93  cnf(c_0_73, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.78/0.93  cnf(c_0_74, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.78/0.93  fof(c_0_75, plain, ![X25, X26]:(~r2_hidden(X25,X26)|m1_subset_1(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.78/0.93  cnf(c_0_76, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.78/0.93  cnf(c_0_77, negated_conjecture, (r2_hidden(k1_mcart_1(esk8_0),k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.78/0.93  cnf(c_0_78, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk8_0))=k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_50]), c_0_45]), c_0_47]), c_0_53])).
% 0.78/0.93  cnf(c_0_79, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk8_0))=k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_50]), c_0_45]), c_0_47]), c_0_53])).
% 0.78/0.93  cnf(c_0_80, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.78/0.93  cnf(c_0_81, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.78/0.93  cnf(c_0_82, negated_conjecture, (esk7_0=X1|~m1_subset_1(X1,esk4_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X3,esk6_0)|esk8_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.78/0.93  cnf(c_0_83, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.78/0.93  cnf(c_0_84, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.78/0.93  cnf(c_0_85, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.78/0.93  cnf(c_0_86, negated_conjecture, (r2_hidden(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.78/0.93  cnf(c_0_87, negated_conjecture, (r2_hidden(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_77]), c_0_79])).
% 0.78/0.93  cnf(c_0_88, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_80, c_0_20])).
% 0.78/0.93  cnf(c_0_89, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_81, c_0_20])).
% 0.78/0.93  cnf(c_0_90, negated_conjecture, (esk7_0=X1|esk8_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk6_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk4_0)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.78/0.93  cnf(c_0_91, negated_conjecture, (k4_tarski(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0))=k1_mcart_1(esk8_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_77]), c_0_79]), c_0_78])).
% 0.78/0.93  cnf(c_0_92, negated_conjecture, (m1_subset_1(k6_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk5_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.78/0.93  cnf(c_0_93, negated_conjecture, (m1_subset_1(k5_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_87])).
% 0.78/0.93  cnf(c_0_94, negated_conjecture, (m1_subset_1(k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0),esk6_0)), inference(spm,[status(thm)],[c_0_88, c_0_50])).
% 0.78/0.93  cnf(c_0_95, negated_conjecture, (k7_mcart_1(esk4_0,esk5_0,esk6_0,esk8_0)=k2_mcart_1(esk8_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_50]), c_0_45]), c_0_47]), c_0_53])).
% 0.78/0.93  cnf(c_0_96, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),X1)!=esk8_0|~m1_subset_1(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_93])]), c_0_36])).
% 0.78/0.93  cnf(c_0_97, negated_conjecture, (k4_tarski(k1_mcart_1(esk8_0),k2_mcart_1(esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_84, c_0_68])).
% 0.78/0.93  cnf(c_0_98, negated_conjecture, (m1_subset_1(k2_mcart_1(esk8_0),esk6_0)), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.78/0.93  cnf(c_0_99, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])]), ['proof']).
% 0.78/0.93  # SZS output end CNFRefutation
% 0.78/0.93  # Proof object total steps             : 100
% 0.78/0.93  # Proof object clause steps            : 67
% 0.78/0.93  # Proof object formula steps           : 33
% 0.78/0.93  # Proof object conjectures             : 35
% 0.78/0.93  # Proof object clause conjectures      : 32
% 0.78/0.93  # Proof object formula conjectures     : 3
% 0.78/0.93  # Proof object initial clauses used    : 26
% 0.78/0.93  # Proof object initial formulas used   : 16
% 0.78/0.93  # Proof object generating inferences   : 28
% 0.78/0.93  # Proof object simplifying inferences  : 38
% 0.78/0.93  # Training examples: 0 positive, 0 negative
% 0.78/0.93  # Parsed axioms                        : 17
% 0.78/0.93  # Removed by relevancy pruning/SinE    : 0
% 0.78/0.93  # Initial clauses                      : 39
% 0.78/0.93  # Removed in clause preprocessing      : 3
% 0.78/0.93  # Initial clauses in saturation        : 36
% 0.78/0.93  # Processed clauses                    : 3017
% 0.78/0.93  # ...of these trivial                  : 337
% 0.78/0.93  # ...subsumed                          : 2042
% 0.78/0.93  # ...remaining for further processing  : 638
% 0.78/0.93  # Other redundant clauses eliminated   : 659
% 0.78/0.93  # Clauses deleted for lack of memory   : 0
% 0.78/0.93  # Backward-subsumed                    : 21
% 0.78/0.93  # Backward-rewritten                   : 66
% 0.78/0.93  # Generated clauses                    : 83558
% 0.78/0.93  # ...of the previous two non-trivial   : 63845
% 0.78/0.93  # Contextual simplify-reflections      : 9
% 0.78/0.93  # Paramodulations                      : 82614
% 0.78/0.93  # Factorizations                       : 288
% 0.78/0.93  # Equation resolutions                 : 659
% 0.78/0.93  # Propositional unsat checks           : 0
% 0.78/0.93  #    Propositional check models        : 0
% 0.78/0.93  #    Propositional check unsatisfiable : 0
% 0.78/0.93  #    Propositional clauses             : 0
% 0.78/0.93  #    Propositional clauses after purity: 0
% 0.78/0.93  #    Propositional unsat core size     : 0
% 0.78/0.93  #    Propositional preprocessing time  : 0.000
% 0.78/0.93  #    Propositional encoding time       : 0.000
% 0.78/0.93  #    Propositional solver time         : 0.000
% 0.78/0.93  #    Success case prop preproc time    : 0.000
% 0.78/0.93  #    Success case prop encoding time   : 0.000
% 0.78/0.93  #    Success case prop solver time     : 0.000
% 0.78/0.93  # Current number of processed clauses  : 507
% 0.78/0.93  #    Positive orientable unit clauses  : 220
% 0.78/0.93  #    Positive unorientable unit clauses: 0
% 0.78/0.93  #    Negative unit clauses             : 5
% 0.78/0.93  #    Non-unit-clauses                  : 282
% 0.78/0.93  # Current number of unprocessed clauses: 59489
% 0.78/0.93  # ...number of literals in the above   : 287183
% 0.78/0.93  # Current number of archived formulas  : 0
% 0.78/0.93  # Current number of archived clauses   : 126
% 0.78/0.93  # Clause-clause subsumption calls (NU) : 33619
% 0.78/0.93  # Rec. Clause-clause subsumption calls : 24938
% 0.78/0.93  # Non-unit clause-clause subsumptions  : 2014
% 0.78/0.93  # Unit Clause-clause subsumption calls : 1405
% 0.78/0.93  # Rewrite failures with RHS unbound    : 0
% 0.78/0.93  # BW rewrite match attempts            : 384
% 0.78/0.93  # BW rewrite match successes           : 21
% 0.78/0.93  # Condensation attempts                : 0
% 0.78/0.93  # Condensation successes               : 0
% 0.78/0.93  # Termbank termtop insertions          : 1316453
% 0.79/0.94  
% 0.79/0.94  # -------------------------------------------------
% 0.79/0.94  # User time                : 0.583 s
% 0.79/0.94  # System time              : 0.020 s
% 0.79/0.94  # Total time               : 0.602 s
% 0.79/0.94  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
