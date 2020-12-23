%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:46:53 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 169 expanded)
%              Number of clauses        :   46 (  72 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  263 ( 938 expanded)
%              Number of equality atoms :   61 ( 178 expanded)
%              Maximal formula depth    :   32 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ! [X6] :
                      ( m1_subset_1(X6,X1)
                     => ! [X7] :
                          ( m1_subset_1(X7,X1)
                         => ! [X8] :
                              ( m1_subset_1(X8,X1)
                             => ( X1 != k1_xboole_0
                               => m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_subset_1)).

fof(t59_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ! [X6] :
                      ( m1_subset_1(X6,X1)
                     => ( X1 != k1_xboole_0
                       => m1_subset_1(k3_enumset1(X2,X3,X4,X5,X6),k1_zfmisc_1(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_subset_1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(t60_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ! [X4] :
                ( m1_subset_1(X4,X1)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X1)
                       => ! [X7] :
                            ( m1_subset_1(X7,X1)
                           => ! [X8] :
                                ( m1_subset_1(X8,X1)
                               => ( X1 != k1_xboole_0
                                 => m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_subset_1])).

fof(c_0_13,plain,(
    ! [X61,X62,X63,X64,X65,X66] :
      ( ~ m1_subset_1(X62,X61)
      | ~ m1_subset_1(X63,X61)
      | ~ m1_subset_1(X64,X61)
      | ~ m1_subset_1(X65,X61)
      | ~ m1_subset_1(X66,X61)
      | X61 = k1_xboole_0
      | m1_subset_1(k3_enumset1(X62,X63,X64,X65,X66),k1_zfmisc_1(X61)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_subset_1])])])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0)
    & m1_subset_1(esk6_0,esk4_0)
    & m1_subset_1(esk7_0,esk4_0)
    & m1_subset_1(esk8_0,esk4_0)
    & m1_subset_1(esk9_0,esk4_0)
    & m1_subset_1(esk10_0,esk4_0)
    & m1_subset_1(esk11_0,esk4_0)
    & esk4_0 != k1_xboole_0
    & ~ m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22] : k5_enumset1(X16,X17,X18,X19,X20,X21,X22) = k2_xboole_0(k2_tarski(X16,X17),k3_enumset1(X18,X19,X20,X21,X22)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29] : k5_enumset1(X23,X24,X25,X26,X27,X28,X29) = k2_xboole_0(k3_enumset1(X23,X24,X25,X26,X27),k2_tarski(X28,X29)) ),
    inference(variable_rename,[status(thm)],[t60_enumset1])).

fof(c_0_17,plain,(
    ! [X58,X59,X60] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(X58))
      | ~ r2_hidden(X60,X59)
      | r2_hidden(X60,X58) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_18,plain,
    ( X2 = k1_xboole_0
    | m1_subset_1(k3_enumset1(X1,X3,X4,X5,X6),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X5,X2)
    | ~ m1_subset_1(X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk11_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X42,X43,X44,X45,X46,X47,X48,X49,X50,X51,X52,X53,X54,X55] :
      ( ( ~ r2_hidden(X48,X47)
        | X48 = X42
        | X48 = X43
        | X48 = X44
        | X48 = X45
        | X48 = X46
        | X47 != k3_enumset1(X42,X43,X44,X45,X46) )
      & ( X49 != X42
        | r2_hidden(X49,X47)
        | X47 != k3_enumset1(X42,X43,X44,X45,X46) )
      & ( X49 != X43
        | r2_hidden(X49,X47)
        | X47 != k3_enumset1(X42,X43,X44,X45,X46) )
      & ( X49 != X44
        | r2_hidden(X49,X47)
        | X47 != k3_enumset1(X42,X43,X44,X45,X46) )
      & ( X49 != X45
        | r2_hidden(X49,X47)
        | X47 != k3_enumset1(X42,X43,X44,X45,X46) )
      & ( X49 != X46
        | r2_hidden(X49,X47)
        | X47 != k3_enumset1(X42,X43,X44,X45,X46) )
      & ( esk3_6(X50,X51,X52,X53,X54,X55) != X50
        | ~ r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)
        | X55 = k3_enumset1(X50,X51,X52,X53,X54) )
      & ( esk3_6(X50,X51,X52,X53,X54,X55) != X51
        | ~ r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)
        | X55 = k3_enumset1(X50,X51,X52,X53,X54) )
      & ( esk3_6(X50,X51,X52,X53,X54,X55) != X52
        | ~ r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)
        | X55 = k3_enumset1(X50,X51,X52,X53,X54) )
      & ( esk3_6(X50,X51,X52,X53,X54,X55) != X53
        | ~ r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)
        | X55 = k3_enumset1(X50,X51,X52,X53,X54) )
      & ( esk3_6(X50,X51,X52,X53,X54,X55) != X54
        | ~ r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)
        | X55 = k3_enumset1(X50,X51,X52,X53,X54) )
      & ( r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)
        | esk3_6(X50,X51,X52,X53,X54,X55) = X50
        | esk3_6(X50,X51,X52,X53,X54,X55) = X51
        | esk3_6(X50,X51,X52,X53,X54,X55) = X52
        | esk3_6(X50,X51,X52,X53,X54,X55) = X53
        | esk3_6(X50,X51,X52,X53,X54,X55) = X54
        | X55 = k3_enumset1(X50,X51,X52,X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X40,X41] :
      ( ( ~ m1_subset_1(X41,X40)
        | r2_hidden(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ r2_hidden(X41,X40)
        | m1_subset_1(X41,X40)
        | v1_xboole_0(X40) )
      & ( ~ m1_subset_1(X41,X40)
        | v1_xboole_0(X41)
        | ~ v1_xboole_0(X40) )
      & ( ~ v1_xboole_0(X41)
        | m1_subset_1(X41,X40)
        | ~ v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_26,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(k3_enumset1(X1,X2,X3,X4,esk11_0),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k2_tarski(esk5_0,esk6_0),k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ( ~ r2_hidden(X32,X31)
        | r1_tarski(X32,X30)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r1_tarski(X33,X30)
        | r2_hidden(X33,X31)
        | X31 != k1_zfmisc_1(X30) )
      & ( ~ r2_hidden(esk2_2(X34,X35),X35)
        | ~ r1_tarski(esk2_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) )
      & ( r2_hidden(esk2_2(X34,X35),X35)
        | r1_tarski(esk2_2(X34,X35),X34)
        | X35 = k1_zfmisc_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X5,esk4_0)
    | ~ r2_hidden(X1,k3_enumset1(X5,X4,X3,X2,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_tarski(esk10_0,esk11_0)),k1_zfmisc_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X15,X14)
      | r1_tarski(k2_xboole_0(X13,X15),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_tarski(esk10_0,esk11_0)),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_tarski(esk10_0,esk11_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)),X8)
    | ~ r1_tarski(k3_enumset1(X3,X4,X5,X6,X7),X8)
    | ~ r1_tarski(k2_tarski(X1,X2),X8) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

fof(c_0_48,plain,(
    ! [X37,X38,X39] :
      ( ( r2_hidden(X37,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( r2_hidden(X38,X39)
        | ~ r1_tarski(k2_tarski(X37,X38),X39) )
      & ( ~ r2_hidden(X37,X39)
        | ~ r2_hidden(X38,X39)
        | r1_tarski(k2_tarski(X37,X38),X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_19])).

fof(c_0_50,plain,(
    ! [X57] : ~ v1_xboole_0(k1_zfmisc_1(X57)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0)
    | ~ r1_tarski(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_58,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0)
    | ~ r2_hidden(esk6_0,esk4_0)
    | ~ r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k3_enumset1(X1,X2,X3,X4,esk11_0),k1_zfmisc_1(esk4_0))
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])]),c_0_61])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k3_enumset1(X1,X2,X3,X4,esk11_0),esk4_0)
    | ~ m1_subset_1(X4,esk4_0)
    | ~ m1_subset_1(X3,esk4_0)
    | ~ m1_subset_1(X2,esk4_0)
    | ~ m1_subset_1(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk10_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk9_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk8_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_67]),c_0_68]),c_0_69])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.62/2.85  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.62/2.85  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.62/2.85  #
% 2.62/2.85  # Preprocessing time       : 0.029 s
% 2.62/2.85  # Presaturation interreduction done
% 2.62/2.85  
% 2.62/2.85  # Proof found!
% 2.62/2.85  # SZS status Theorem
% 2.62/2.85  # SZS output start CNFRefutation
% 2.62/2.85  fof(t61_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_subset_1)).
% 2.62/2.85  fof(t59_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k3_enumset1(X2,X3,X4,X5,X6),k1_zfmisc_1(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_subset_1)).
% 2.62/2.85  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_enumset1)).
% 2.62/2.85  fof(t60_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_enumset1)).
% 2.62/2.85  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.62/2.85  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.62/2.85  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.62/2.85  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.62/2.85  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.62/2.85  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.62/2.85  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.62/2.85  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.62/2.85  fof(c_0_12, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,X1)=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(m1_subset_1(X4,X1)=>![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X1)=>![X8]:(m1_subset_1(X8,X1)=>(X1!=k1_xboole_0=>m1_subset_1(k5_enumset1(X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(X1))))))))))), inference(assume_negation,[status(cth)],[t61_subset_1])).
% 2.62/2.85  fof(c_0_13, plain, ![X61, X62, X63, X64, X65, X66]:(~m1_subset_1(X62,X61)|(~m1_subset_1(X63,X61)|(~m1_subset_1(X64,X61)|(~m1_subset_1(X65,X61)|(~m1_subset_1(X66,X61)|(X61=k1_xboole_0|m1_subset_1(k3_enumset1(X62,X63,X64,X65,X66),k1_zfmisc_1(X61)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_subset_1])])])).
% 2.62/2.85  fof(c_0_14, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)&(m1_subset_1(esk6_0,esk4_0)&(m1_subset_1(esk7_0,esk4_0)&(m1_subset_1(esk8_0,esk4_0)&(m1_subset_1(esk9_0,esk4_0)&(m1_subset_1(esk10_0,esk4_0)&(m1_subset_1(esk11_0,esk4_0)&(esk4_0!=k1_xboole_0&~m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 2.62/2.85  fof(c_0_15, plain, ![X16, X17, X18, X19, X20, X21, X22]:k5_enumset1(X16,X17,X18,X19,X20,X21,X22)=k2_xboole_0(k2_tarski(X16,X17),k3_enumset1(X18,X19,X20,X21,X22)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 2.62/2.85  fof(c_0_16, plain, ![X23, X24, X25, X26, X27, X28, X29]:k5_enumset1(X23,X24,X25,X26,X27,X28,X29)=k2_xboole_0(k3_enumset1(X23,X24,X25,X26,X27),k2_tarski(X28,X29)), inference(variable_rename,[status(thm)],[t60_enumset1])).
% 2.62/2.85  fof(c_0_17, plain, ![X58, X59, X60]:(~m1_subset_1(X59,k1_zfmisc_1(X58))|(~r2_hidden(X60,X59)|r2_hidden(X60,X58))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 2.62/2.85  cnf(c_0_18, plain, (X2=k1_xboole_0|m1_subset_1(k3_enumset1(X1,X3,X4,X5,X6),k1_zfmisc_1(X2))|~m1_subset_1(X1,X2)|~m1_subset_1(X3,X2)|~m1_subset_1(X4,X2)|~m1_subset_1(X5,X2)|~m1_subset_1(X6,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.62/2.85  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk11_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_20, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  fof(c_0_21, plain, ![X42, X43, X44, X45, X46, X47, X48, X49, X50, X51, X52, X53, X54, X55]:(((~r2_hidden(X48,X47)|(X48=X42|X48=X43|X48=X44|X48=X45|X48=X46)|X47!=k3_enumset1(X42,X43,X44,X45,X46))&(((((X49!=X42|r2_hidden(X49,X47)|X47!=k3_enumset1(X42,X43,X44,X45,X46))&(X49!=X43|r2_hidden(X49,X47)|X47!=k3_enumset1(X42,X43,X44,X45,X46)))&(X49!=X44|r2_hidden(X49,X47)|X47!=k3_enumset1(X42,X43,X44,X45,X46)))&(X49!=X45|r2_hidden(X49,X47)|X47!=k3_enumset1(X42,X43,X44,X45,X46)))&(X49!=X46|r2_hidden(X49,X47)|X47!=k3_enumset1(X42,X43,X44,X45,X46))))&((((((esk3_6(X50,X51,X52,X53,X54,X55)!=X50|~r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)|X55=k3_enumset1(X50,X51,X52,X53,X54))&(esk3_6(X50,X51,X52,X53,X54,X55)!=X51|~r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)|X55=k3_enumset1(X50,X51,X52,X53,X54)))&(esk3_6(X50,X51,X52,X53,X54,X55)!=X52|~r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)|X55=k3_enumset1(X50,X51,X52,X53,X54)))&(esk3_6(X50,X51,X52,X53,X54,X55)!=X53|~r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)|X55=k3_enumset1(X50,X51,X52,X53,X54)))&(esk3_6(X50,X51,X52,X53,X54,X55)!=X54|~r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)|X55=k3_enumset1(X50,X51,X52,X53,X54)))&(r2_hidden(esk3_6(X50,X51,X52,X53,X54,X55),X55)|(esk3_6(X50,X51,X52,X53,X54,X55)=X50|esk3_6(X50,X51,X52,X53,X54,X55)=X51|esk3_6(X50,X51,X52,X53,X54,X55)=X52|esk3_6(X50,X51,X52,X53,X54,X55)=X53|esk3_6(X50,X51,X52,X53,X54,X55)=X54)|X55=k3_enumset1(X50,X51,X52,X53,X54)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 2.62/2.85  cnf(c_0_22, negated_conjecture, (~m1_subset_1(k5_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),k1_zfmisc_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_23, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.62/2.85  cnf(c_0_24, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.62/2.85  fof(c_0_25, plain, ![X40, X41]:(((~m1_subset_1(X41,X40)|r2_hidden(X41,X40)|v1_xboole_0(X40))&(~r2_hidden(X41,X40)|m1_subset_1(X41,X40)|v1_xboole_0(X40)))&((~m1_subset_1(X41,X40)|v1_xboole_0(X41)|~v1_xboole_0(X40))&(~v1_xboole_0(X41)|m1_subset_1(X41,X40)|~v1_xboole_0(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 2.62/2.85  fof(c_0_26, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 2.62/2.85  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.62/2.85  cnf(c_0_28, negated_conjecture, (m1_subset_1(k3_enumset1(X1,X2,X3,X4,esk11_0),k1_zfmisc_1(esk4_0))|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 2.62/2.85  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.62/2.85  cnf(c_0_30, negated_conjecture, (~m1_subset_1(k2_xboole_0(k2_tarski(esk5_0,esk6_0),k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0)),k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 2.62/2.85  cnf(c_0_31, plain, (k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7))), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 2.62/2.85  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.62/2.85  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.62/2.85  fof(c_0_34, plain, ![X30, X31, X32, X33, X34, X35]:(((~r2_hidden(X32,X31)|r1_tarski(X32,X30)|X31!=k1_zfmisc_1(X30))&(~r1_tarski(X33,X30)|r2_hidden(X33,X31)|X31!=k1_zfmisc_1(X30)))&((~r2_hidden(esk2_2(X34,X35),X35)|~r1_tarski(esk2_2(X34,X35),X34)|X35=k1_zfmisc_1(X34))&(r2_hidden(esk2_2(X34,X35),X35)|r1_tarski(esk2_2(X34,X35),X34)|X35=k1_zfmisc_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 2.62/2.85  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X5,esk4_0)|~r2_hidden(X1,k3_enumset1(X5,X4,X3,X2,esk11_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 2.62/2.85  cnf(c_0_36, plain, (r2_hidden(X1,k3_enumset1(X1,X2,X3,X4,X5))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 2.62/2.85  cnf(c_0_37, negated_conjecture, (~m1_subset_1(k2_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_tarski(esk10_0,esk11_0)),k1_zfmisc_1(esk4_0))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 2.62/2.85  cnf(c_0_38, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_32, c_0_33])).
% 2.62/2.85  cnf(c_0_39, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.62/2.85  fof(c_0_40, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X15,X14)|r1_tarski(k2_xboole_0(X13,X15),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 2.62/2.85  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 2.62/2.85  cnf(c_0_42, negated_conjecture, (~r2_hidden(k2_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_tarski(esk10_0,esk11_0)),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 2.62/2.85  cnf(c_0_43, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_39])).
% 2.62/2.85  cnf(c_0_44, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 2.62/2.85  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_19])).
% 2.62/2.85  cnf(c_0_46, negated_conjecture, (~r1_tarski(k2_xboole_0(k3_enumset1(esk5_0,esk6_0,esk7_0,esk8_0,esk9_0),k2_tarski(esk10_0,esk11_0)),esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 2.62/2.85  cnf(c_0_47, plain, (r1_tarski(k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k2_tarski(X6,X7)),X8)|~r1_tarski(k3_enumset1(X3,X4,X5,X6,X7),X8)|~r1_tarski(k2_tarski(X1,X2),X8)), inference(spm,[status(thm)],[c_0_44, c_0_31])).
% 2.62/2.85  fof(c_0_48, plain, ![X37, X38, X39]:(((r2_hidden(X37,X39)|~r1_tarski(k2_tarski(X37,X38),X39))&(r2_hidden(X38,X39)|~r1_tarski(k2_tarski(X37,X38),X39)))&(~r2_hidden(X37,X39)|~r2_hidden(X38,X39)|r1_tarski(k2_tarski(X37,X38),X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 2.62/2.85  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_45, c_0_19])).
% 2.62/2.85  fof(c_0_50, plain, ![X57]:~v1_xboole_0(k1_zfmisc_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 2.62/2.85  cnf(c_0_51, negated_conjecture, (~r1_tarski(k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0)|~r1_tarski(k2_tarski(esk5_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.62/2.85  cnf(c_0_52, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.62/2.85  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_49, c_0_19])).
% 2.62/2.85  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_56, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.62/2.85  cnf(c_0_57, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.62/2.85  cnf(c_0_58, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 2.62/2.85  cnf(c_0_59, negated_conjecture, (~r1_tarski(k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0)|~r2_hidden(esk6_0,esk4_0)|~r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 2.62/2.85  cnf(c_0_60, negated_conjecture, (r2_hidden(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 2.62/2.85  cnf(c_0_61, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 2.62/2.85  cnf(c_0_62, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_56])).
% 2.62/2.85  cnf(c_0_63, negated_conjecture, (r2_hidden(k3_enumset1(X1,X2,X3,X4,esk11_0),k1_zfmisc_1(esk4_0))|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_28]), c_0_58])).
% 2.62/2.85  cnf(c_0_64, negated_conjecture, (~r1_tarski(k3_enumset1(esk7_0,esk8_0,esk9_0,esk10_0,esk11_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])]), c_0_61])])).
% 2.62/2.85  cnf(c_0_65, negated_conjecture, (r1_tarski(k3_enumset1(X1,X2,X3,X4,esk11_0),esk4_0)|~m1_subset_1(X4,esk4_0)|~m1_subset_1(X3,esk4_0)|~m1_subset_1(X2,esk4_0)|~m1_subset_1(X1,esk4_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 2.62/2.85  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk10_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk9_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk8_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.62/2.85  cnf(c_0_70, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_67]), c_0_68]), c_0_69])]), ['proof']).
% 2.62/2.85  # SZS output end CNFRefutation
% 2.62/2.85  # Proof object total steps             : 71
% 2.62/2.85  # Proof object clause steps            : 46
% 2.62/2.85  # Proof object formula steps           : 25
% 2.62/2.85  # Proof object conjectures             : 30
% 2.62/2.85  # Proof object clause conjectures      : 27
% 2.62/2.85  # Proof object formula conjectures     : 3
% 2.62/2.85  # Proof object initial clauses used    : 22
% 2.62/2.85  # Proof object initial formulas used   : 12
% 2.62/2.85  # Proof object generating inferences   : 16
% 2.62/2.85  # Proof object simplifying inferences  : 19
% 2.62/2.85  # Training examples: 0 positive, 0 negative
% 2.62/2.85  # Parsed axioms                        : 12
% 2.62/2.85  # Removed by relevancy pruning/SinE    : 0
% 2.62/2.85  # Initial clauses                      : 40
% 2.62/2.85  # Removed in clause preprocessing      : 1
% 2.62/2.85  # Initial clauses in saturation        : 39
% 2.62/2.85  # Processed clauses                    : 18072
% 2.62/2.85  # ...of these trivial                  : 7
% 2.62/2.85  # ...subsumed                          : 13761
% 2.62/2.85  # ...remaining for further processing  : 4304
% 2.62/2.85  # Other redundant clauses eliminated   : 188
% 2.62/2.85  # Clauses deleted for lack of memory   : 0
% 2.62/2.85  # Backward-subsumed                    : 262
% 2.62/2.85  # Backward-rewritten                   : 3671
% 2.62/2.85  # Generated clauses                    : 129546
% 2.62/2.85  # ...of the previous two non-trivial   : 128820
% 2.62/2.85  # Contextual simplify-reflections      : 1285
% 2.62/2.85  # Paramodulations                      : 129223
% 2.62/2.85  # Factorizations                       : 134
% 2.62/2.85  # Equation resolutions                 : 188
% 2.62/2.85  # Propositional unsat checks           : 0
% 2.62/2.85  #    Propositional check models        : 0
% 2.62/2.85  #    Propositional check unsatisfiable : 0
% 2.62/2.85  #    Propositional clauses             : 0
% 2.62/2.85  #    Propositional clauses after purity: 0
% 2.62/2.85  #    Propositional unsat core size     : 0
% 2.62/2.85  #    Propositional preprocessing time  : 0.000
% 2.62/2.85  #    Propositional encoding time       : 0.000
% 2.62/2.85  #    Propositional solver time         : 0.000
% 2.62/2.85  #    Success case prop preproc time    : 0.000
% 2.62/2.85  #    Success case prop encoding time   : 0.000
% 2.62/2.85  #    Success case prop solver time     : 0.000
% 2.62/2.85  # Current number of processed clauses  : 318
% 2.62/2.85  #    Positive orientable unit clauses  : 20
% 2.62/2.85  #    Positive unorientable unit clauses: 1
% 2.62/2.85  #    Negative unit clauses             : 9
% 2.62/2.85  #    Non-unit-clauses                  : 288
% 2.62/2.85  # Current number of unprocessed clauses: 81682
% 2.62/2.85  # ...number of literals in the above   : 454822
% 2.62/2.85  # Current number of archived formulas  : 0
% 2.62/2.85  # Current number of archived clauses   : 3979
% 2.62/2.85  # Clause-clause subsumption calls (NU) : 14645307
% 2.62/2.85  # Rec. Clause-clause subsumption calls : 5243780
% 2.62/2.85  # Non-unit clause-clause subsumptions  : 15176
% 2.62/2.85  # Unit Clause-clause subsumption calls : 8337
% 2.62/2.85  # Rewrite failures with RHS unbound    : 0
% 2.62/2.85  # BW rewrite match attempts            : 29
% 2.62/2.85  # BW rewrite match successes           : 9
% 2.62/2.85  # Condensation attempts                : 0
% 2.62/2.85  # Condensation successes               : 0
% 2.62/2.85  # Termbank termtop insertions          : 2622186
% 2.62/2.85  
% 2.62/2.85  # -------------------------------------------------
% 2.62/2.85  # User time                : 2.460 s
% 2.62/2.85  # System time              : 0.038 s
% 2.62/2.85  # Total time               : 2.498 s
% 2.62/2.85  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
