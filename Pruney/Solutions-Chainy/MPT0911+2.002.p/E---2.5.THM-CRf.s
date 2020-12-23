%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:14 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  112 (3417 expanded)
%              Number of clauses        :   77 (1566 expanded)
%              Number of leaves         :   17 ( 841 expanded)
%              Depth                    :   20
%              Number of atoms          :  284 (12019 expanded)
%              Number of equality atoms :  159 (7699 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(d4_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(t55_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & X4 != k1_xboole_0 )
    <=> k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,negated_conjecture,(
    ! [X85,X86,X87] :
      ( m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))
      & ( ~ m1_subset_1(X85,esk7_0)
        | ~ m1_subset_1(X86,esk8_0)
        | ~ m1_subset_1(X87,esk9_0)
        | esk11_0 != k3_mcart_1(X85,X86,X87)
        | esk10_0 = X87 )
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k1_xboole_0
      & esk10_0 != k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_19,plain,(
    ! [X54,X55,X56] : k3_zfmisc_1(X54,X55,X56) = k2_zfmisc_1(k2_zfmisc_1(X54,X55),X56) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X46,X47] :
      ( ( ~ m1_subset_1(X46,k1_zfmisc_1(X47))
        | r1_tarski(X46,X47) )
      & ( ~ r1_tarski(X46,X47)
        | m1_subset_1(X46,k1_zfmisc_1(X47)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X28] : r1_tarski(k1_xboole_0,X28) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( ~ m1_subset_1(X44,X45)
      | v1_xboole_0(X45)
      | r2_hidden(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X41] : ~ v1_xboole_0(k1_zfmisc_1(X41)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_28,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X64,X66,X67,X68,X69] :
      ( ( r2_hidden(esk6_1(X64),X64)
        | X64 = k1_xboole_0 )
      & ( ~ r2_hidden(X66,X64)
        | esk6_1(X64) != k4_mcart_1(X66,X67,X68,X69)
        | X64 = k1_xboole_0 )
      & ( ~ r2_hidden(X67,X64)
        | esk6_1(X64) != k4_mcart_1(X66,X67,X68,X69)
        | X64 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_34,plain,(
    ! [X57,X58,X59,X60] : k4_zfmisc_1(X57,X58,X59,X60) = k2_zfmisc_1(k3_zfmisc_1(X57,X58,X59),X60) ),
    inference(variable_rename,[status(thm)],[d4_zfmisc_1])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X74,X75,X76,X77] :
      ( ( X74 = k1_xboole_0
        | X75 = k1_xboole_0
        | X76 = k1_xboole_0
        | X77 = k1_xboole_0
        | k4_zfmisc_1(X74,X75,X76,X77) != k1_xboole_0 )
      & ( X74 != k1_xboole_0
        | k4_zfmisc_1(X74,X75,X76,X77) = k1_xboole_0 )
      & ( X75 != k1_xboole_0
        | k4_zfmisc_1(X74,X75,X76,X77) = k1_xboole_0 )
      & ( X76 != k1_xboole_0
        | k4_zfmisc_1(X74,X75,X76,X77) = k1_xboole_0 )
      & ( X77 != k1_xboole_0
        | k4_zfmisc_1(X74,X75,X76,X77) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).

cnf(c_0_40,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | m1_subset_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k4_zfmisc_1(X2,X3,X4,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( k4_zfmisc_1(X1,X2,X3,X4) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) ),
    inference(rw,[status(thm)],[c_0_40,c_0_24])).

fof(c_0_46,plain,(
    ! [X70,X71,X72,X73] :
      ( ( k5_mcart_1(X70,X71,X72,X73) = k1_mcart_1(k1_mcart_1(X73))
        | ~ m1_subset_1(X73,k3_zfmisc_1(X70,X71,X72))
        | X70 = k1_xboole_0
        | X71 = k1_xboole_0
        | X72 = k1_xboole_0 )
      & ( k6_mcart_1(X70,X71,X72,X73) = k2_mcart_1(k1_mcart_1(X73))
        | ~ m1_subset_1(X73,k3_zfmisc_1(X70,X71,X72))
        | X70 = k1_xboole_0
        | X71 = k1_xboole_0
        | X72 = k1_xboole_0 )
      & ( k7_mcart_1(X70,X71,X72,X73) = k2_mcart_1(X73)
        | ~ m1_subset_1(X73,k3_zfmisc_1(X70,X71,X72))
        | X70 = k1_xboole_0
        | X71 = k1_xboole_0
        | X72 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_47,plain,(
    ! [X25,X26] :
      ( ( r1_tarski(X25,X26)
        | X25 != X26 )
      & ( r1_tarski(X26,X25)
        | X25 != X26 )
      & ( ~ r1_tarski(X25,X26)
        | ~ r1_tarski(X26,X25)
        | X25 = X26 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),k1_zfmisc_1(X1))
    | r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( k4_zfmisc_1(X2,X3,X1,X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),k1_zfmisc_1(X1))
    | r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k1_xboole_0
    | k4_zfmisc_1(X1,X2,X3,X4) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_63,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),X1)
    | r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( esk10_0 != k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) = k2_mcart_1(esk11_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_30]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_69,plain,
    ( X4 = k1_xboole_0
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_62,c_0_45])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0) = k1_xboole_0
    | r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_65]),c_0_66])).

fof(c_0_72,plain,(
    ! [X61,X62,X63] :
      ( ( r2_hidden(k1_mcart_1(X61),X62)
        | ~ r2_hidden(X61,k2_zfmisc_1(X62,X63)) )
      & ( r2_hidden(k2_mcart_1(X61),X63)
        | ~ r2_hidden(X61,k2_zfmisc_1(X62,X63)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_73,negated_conjecture,
    ( k2_mcart_1(esk11_0) != esk10_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),c_0_59]),c_0_60]),c_0_61])).

fof(c_0_75,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,k2_zfmisc_1(X33,X34))
      | k4_tarski(esk4_1(X32),esk5_1(X32)) = X32 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_76,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_74])).

cnf(c_0_78,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_79,plain,(
    ! [X78,X79] :
      ( k1_mcart_1(k4_tarski(X78,X79)) = X78
      & k2_mcart_1(k4_tarski(X78,X79)) = X79 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_80,plain,
    ( k4_tarski(esk4_1(X1),esk5_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk11_0),k2_zfmisc_1(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_78,c_0_24])).

cnf(c_0_83,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k4_tarski(esk4_1(k1_mcart_1(esk11_0)),esk5_1(k1_mcart_1(esk11_0))) = k1_mcart_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk11_0)) = k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_30]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_86,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( esk4_1(k1_mcart_1(esk11_0)) = k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_88,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_24])).

cnf(c_0_89,negated_conjecture,
    ( k4_tarski(esk4_1(esk11_0),esk5_1(esk11_0)) = esk11_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_77])).

fof(c_0_90,plain,(
    ! [X51,X52,X53] : k3_mcart_1(X51,X52,X53) = k4_tarski(k4_tarski(X51,X52),X53) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_91,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_92,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk5_1(k1_mcart_1(esk11_0))) = k1_mcart_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk11_0)) = k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_30]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_94,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_95,negated_conjecture,
    ( esk4_1(esk11_0) = k1_mcart_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_89])).

cnf(c_0_96,negated_conjecture,
    ( esk10_0 = X3
    | ~ m1_subset_1(X1,esk7_0)
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X3,esk9_0)
    | esk11_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_97,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_98,negated_conjecture,
    ( esk5_1(k1_mcart_1(esk11_0)) = k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_81]),c_0_93])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_81]),c_0_85])).

cnf(c_0_101,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk11_0),esk5_1(esk11_0)) = esk11_0 ),
    inference(rw,[status(thm)],[c_0_89,c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( esk10_0 = X3
    | esk11_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk9_0)
    | ~ m1_subset_1(X2,esk8_0)
    | ~ m1_subset_1(X1,esk7_0) ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)) = k1_mcart_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_98])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( esk5_1(esk11_0) = k2_mcart_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(k2_mcart_1(esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_77])).

cnf(c_0_108,negated_conjecture,
    ( esk10_0 = X1
    | k4_tarski(k1_mcart_1(esk11_0),X1) != esk11_0
    | ~ m1_subset_1(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_105])])).

cnf(c_0_109,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk11_0),k2_mcart_1(esk11_0)) = esk11_0 ),
    inference(rw,[status(thm)],[c_0_101,c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_107])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_110])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:15:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.60  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.38/0.60  # and selection function SelectNegativeLiterals.
% 0.38/0.60  #
% 0.38/0.60  # Preprocessing time       : 0.029 s
% 0.38/0.60  # Presaturation interreduction done
% 0.38/0.60  
% 0.38/0.60  # Proof found!
% 0.38/0.60  # SZS status Theorem
% 0.38/0.60  # SZS output start CNFRefutation
% 0.38/0.60  fof(t71_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 0.38/0.60  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.38/0.60  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.38/0.60  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.38/0.60  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.38/0.60  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.38/0.60  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.38/0.60  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.38/0.60  fof(d4_zfmisc_1, axiom, ![X1, X2, X3, X4]:k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 0.38/0.60  fof(t55_mcart_1, axiom, ![X1, X2, X3, X4]:((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&X4!=k1_xboole_0)<=>k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 0.38/0.60  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.38/0.60  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.38/0.60  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.38/0.60  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.38/0.60  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.38/0.60  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.38/0.60  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.38/0.60  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X8))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k7_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t71_mcart_1])).
% 0.38/0.60  fof(c_0_18, negated_conjecture, ![X85, X86, X87]:(m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))&((~m1_subset_1(X85,esk7_0)|(~m1_subset_1(X86,esk8_0)|(~m1_subset_1(X87,esk9_0)|(esk11_0!=k3_mcart_1(X85,X86,X87)|esk10_0=X87))))&(((esk7_0!=k1_xboole_0&esk8_0!=k1_xboole_0)&esk9_0!=k1_xboole_0)&esk10_0!=k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.38/0.60  fof(c_0_19, plain, ![X54, X55, X56]:k3_zfmisc_1(X54,X55,X56)=k2_zfmisc_1(k2_zfmisc_1(X54,X55),X56), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.38/0.60  fof(c_0_20, plain, ![X46, X47]:((~m1_subset_1(X46,k1_zfmisc_1(X47))|r1_tarski(X46,X47))&(~r1_tarski(X46,X47)|m1_subset_1(X46,k1_zfmisc_1(X47)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.38/0.60  fof(c_0_21, plain, ![X28]:r1_tarski(k1_xboole_0,X28), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.38/0.60  fof(c_0_22, plain, ![X44, X45]:(~m1_subset_1(X44,X45)|(v1_xboole_0(X45)|r2_hidden(X44,X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.38/0.60  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk11_0,k3_zfmisc_1(esk7_0,esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.60  cnf(c_0_24, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.38/0.60  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.60  cnf(c_0_26, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.38/0.60  fof(c_0_27, plain, ![X41]:~v1_xboole_0(k1_zfmisc_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.38/0.60  fof(c_0_28, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.38/0.60  cnf(c_0_29, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.38/0.60  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.38/0.60  cnf(c_0_31, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.38/0.60  cnf(c_0_32, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.38/0.60  fof(c_0_33, plain, ![X64, X66, X67, X68, X69]:((r2_hidden(esk6_1(X64),X64)|X64=k1_xboole_0)&((~r2_hidden(X66,X64)|esk6_1(X64)!=k4_mcart_1(X66,X67,X68,X69)|X64=k1_xboole_0)&(~r2_hidden(X67,X64)|esk6_1(X64)!=k4_mcart_1(X66,X67,X68,X69)|X64=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.38/0.60  fof(c_0_34, plain, ![X57, X58, X59, X60]:k4_zfmisc_1(X57,X58,X59,X60)=k2_zfmisc_1(k3_zfmisc_1(X57,X58,X59),X60), inference(variable_rename,[status(thm)],[d4_zfmisc_1])).
% 0.38/0.60  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.38/0.60  cnf(c_0_36, negated_conjecture, (r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.38/0.60  cnf(c_0_37, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_31]), c_0_32])).
% 0.38/0.60  cnf(c_0_38, plain, (r2_hidden(esk6_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.38/0.60  fof(c_0_39, plain, ![X74, X75, X76, X77]:((X74=k1_xboole_0|X75=k1_xboole_0|X76=k1_xboole_0|X77=k1_xboole_0|k4_zfmisc_1(X74,X75,X76,X77)!=k1_xboole_0)&((((X74!=k1_xboole_0|k4_zfmisc_1(X74,X75,X76,X77)=k1_xboole_0)&(X75!=k1_xboole_0|k4_zfmisc_1(X74,X75,X76,X77)=k1_xboole_0))&(X76!=k1_xboole_0|k4_zfmisc_1(X74,X75,X76,X77)=k1_xboole_0))&(X77!=k1_xboole_0|k4_zfmisc_1(X74,X75,X76,X77)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_mcart_1])])])).
% 0.38/0.60  cnf(c_0_40, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k3_zfmisc_1(X1,X2,X3),X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.38/0.60  fof(c_0_41, plain, ![X42, X43]:(~r2_hidden(X42,X43)|m1_subset_1(X42,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.38/0.60  cnf(c_0_42, negated_conjecture, (r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.38/0.60  cnf(c_0_43, plain, (r2_hidden(esk6_1(X1),X1)|r2_hidden(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.38/0.60  cnf(c_0_44, plain, (k4_zfmisc_1(X2,X3,X4,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.60  cnf(c_0_45, plain, (k4_zfmisc_1(X1,X2,X3,X4)=k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)), inference(rw,[status(thm)],[c_0_40, c_0_24])).
% 0.38/0.60  fof(c_0_46, plain, ![X70, X71, X72, X73]:(((k5_mcart_1(X70,X71,X72,X73)=k1_mcart_1(k1_mcart_1(X73))|~m1_subset_1(X73,k3_zfmisc_1(X70,X71,X72))|(X70=k1_xboole_0|X71=k1_xboole_0|X72=k1_xboole_0))&(k6_mcart_1(X70,X71,X72,X73)=k2_mcart_1(k1_mcart_1(X73))|~m1_subset_1(X73,k3_zfmisc_1(X70,X71,X72))|(X70=k1_xboole_0|X71=k1_xboole_0|X72=k1_xboole_0)))&(k7_mcart_1(X70,X71,X72,X73)=k2_mcart_1(X73)|~m1_subset_1(X73,k3_zfmisc_1(X70,X71,X72))|(X70=k1_xboole_0|X71=k1_xboole_0|X72=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.38/0.60  fof(c_0_47, plain, ![X25, X26]:(((r1_tarski(X25,X26)|X25!=X26)&(r1_tarski(X26,X25)|X25!=X26))&(~r1_tarski(X25,X26)|~r1_tarski(X26,X25)|X25=X26)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.38/0.60  cnf(c_0_48, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.38/0.60  cnf(c_0_49, negated_conjecture, (r2_hidden(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),k1_zfmisc_1(X1))|r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.38/0.60  cnf(c_0_50, plain, (k4_zfmisc_1(X2,X3,X1,X4)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.60  cnf(c_0_51, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4),X1)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.38/0.60  cnf(c_0_52, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.60  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.38/0.60  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.38/0.60  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),k1_zfmisc_1(X1))|r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.38/0.60  cnf(c_0_56, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X1),X4)=k1_xboole_0|X1!=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_45])).
% 0.38/0.60  cnf(c_0_57, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_51])).
% 0.38/0.60  cnf(c_0_58, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_52, c_0_24])).
% 0.38/0.60  cnf(c_0_59, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.60  cnf(c_0_60, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.60  cnf(c_0_61, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.60  cnf(c_0_62, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k1_xboole_0|k4_zfmisc_1(X1,X2,X3,X4)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.38/0.60  cnf(c_0_63, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_26])).
% 0.38/0.60  cnf(c_0_64, negated_conjecture, (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0),X1)|r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.38/0.60  cnf(c_0_65, plain, (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),k1_xboole_0),X3)=k1_xboole_0), inference(er,[status(thm)],[c_0_56])).
% 0.38/0.60  cnf(c_0_66, plain, (k2_zfmisc_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_57])).
% 0.38/0.60  cnf(c_0_67, negated_conjecture, (esk10_0!=k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.60  cnf(c_0_68, negated_conjecture, (k7_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)=k2_mcart_1(esk11_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_30]), c_0_59]), c_0_60]), c_0_61])).
% 0.38/0.60  cnf(c_0_69, plain, (X4=k1_xboole_0|X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_62, c_0_45])).
% 0.38/0.60  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0)=k1_xboole_0|r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.38/0.60  cnf(c_0_71, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_65]), c_0_66])).
% 0.38/0.60  fof(c_0_72, plain, ![X61, X62, X63]:((r2_hidden(k1_mcart_1(X61),X62)|~r2_hidden(X61,k2_zfmisc_1(X62,X63)))&(r2_hidden(k2_mcart_1(X61),X63)|~r2_hidden(X61,k2_zfmisc_1(X62,X63)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.38/0.60  cnf(c_0_73, negated_conjecture, (k2_mcart_1(esk11_0)!=esk10_0), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.38/0.60  cnf(c_0_74, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), c_0_59]), c_0_60]), c_0_61])).
% 0.38/0.60  fof(c_0_75, plain, ![X32, X33, X34]:(~r2_hidden(X32,k2_zfmisc_1(X33,X34))|k4_tarski(esk4_1(X32),esk5_1(X32))=X32), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.38/0.60  cnf(c_0_76, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.38/0.60  cnf(c_0_77, negated_conjecture, (r2_hidden(esk11_0,k2_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0),esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_74])).
% 0.38/0.60  cnf(c_0_78, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.60  fof(c_0_79, plain, ![X78, X79]:(k1_mcart_1(k4_tarski(X78,X79))=X78&k2_mcart_1(k4_tarski(X78,X79))=X79), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.38/0.60  cnf(c_0_80, plain, (k4_tarski(esk4_1(X1),esk5_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.38/0.60  cnf(c_0_81, negated_conjecture, (r2_hidden(k1_mcart_1(esk11_0),k2_zfmisc_1(esk7_0,esk8_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.38/0.60  cnf(c_0_82, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_78, c_0_24])).
% 0.38/0.60  cnf(c_0_83, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.38/0.60  cnf(c_0_84, negated_conjecture, (k4_tarski(esk4_1(k1_mcart_1(esk11_0)),esk5_1(k1_mcart_1(esk11_0)))=k1_mcart_1(esk11_0)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.38/0.60  cnf(c_0_85, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk11_0))=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_30]), c_0_59]), c_0_60]), c_0_61])).
% 0.38/0.60  cnf(c_0_86, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.38/0.60  cnf(c_0_87, negated_conjecture, (esk4_1(k1_mcart_1(esk11_0))=k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 0.38/0.60  cnf(c_0_88, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_86, c_0_24])).
% 0.38/0.60  cnf(c_0_89, negated_conjecture, (k4_tarski(esk4_1(esk11_0),esk5_1(esk11_0))=esk11_0), inference(spm,[status(thm)],[c_0_80, c_0_77])).
% 0.38/0.60  fof(c_0_90, plain, ![X51, X52, X53]:k3_mcart_1(X51,X52,X53)=k4_tarski(k4_tarski(X51,X52),X53), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.38/0.60  cnf(c_0_91, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.38/0.60  cnf(c_0_92, negated_conjecture, (k4_tarski(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk5_1(k1_mcart_1(esk11_0)))=k1_mcart_1(esk11_0)), inference(rw,[status(thm)],[c_0_84, c_0_87])).
% 0.38/0.60  cnf(c_0_93, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk11_0))=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_30]), c_0_59]), c_0_60]), c_0_61])).
% 0.38/0.60  cnf(c_0_94, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.38/0.60  cnf(c_0_95, negated_conjecture, (esk4_1(esk11_0)=k1_mcart_1(esk11_0)), inference(spm,[status(thm)],[c_0_83, c_0_89])).
% 0.38/0.60  cnf(c_0_96, negated_conjecture, (esk10_0=X3|~m1_subset_1(X1,esk7_0)|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X3,esk9_0)|esk11_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.38/0.60  cnf(c_0_97, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.38/0.60  cnf(c_0_98, negated_conjecture, (esk5_1(k1_mcart_1(esk11_0))=k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.38/0.60  cnf(c_0_99, negated_conjecture, (r2_hidden(k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_81]), c_0_93])).
% 0.38/0.60  cnf(c_0_100, negated_conjecture, (r2_hidden(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_81]), c_0_85])).
% 0.38/0.60  cnf(c_0_101, negated_conjecture, (k4_tarski(k1_mcart_1(esk11_0),esk5_1(esk11_0))=esk11_0), inference(rw,[status(thm)],[c_0_89, c_0_95])).
% 0.38/0.60  cnf(c_0_102, negated_conjecture, (esk10_0=X3|esk11_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk9_0)|~m1_subset_1(X2,esk8_0)|~m1_subset_1(X1,esk7_0)), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.38/0.60  cnf(c_0_103, negated_conjecture, (k4_tarski(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0))=k1_mcart_1(esk11_0)), inference(rw,[status(thm)],[c_0_92, c_0_98])).
% 0.38/0.60  cnf(c_0_104, negated_conjecture, (m1_subset_1(k6_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk8_0)), inference(spm,[status(thm)],[c_0_48, c_0_99])).
% 0.38/0.60  cnf(c_0_105, negated_conjecture, (m1_subset_1(k5_mcart_1(esk7_0,esk8_0,esk9_0,esk11_0),esk7_0)), inference(spm,[status(thm)],[c_0_48, c_0_100])).
% 0.38/0.60  cnf(c_0_106, negated_conjecture, (esk5_1(esk11_0)=k2_mcart_1(esk11_0)), inference(spm,[status(thm)],[c_0_91, c_0_101])).
% 0.38/0.60  cnf(c_0_107, negated_conjecture, (r2_hidden(k2_mcart_1(esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_94, c_0_77])).
% 0.38/0.60  cnf(c_0_108, negated_conjecture, (esk10_0=X1|k4_tarski(k1_mcart_1(esk11_0),X1)!=esk11_0|~m1_subset_1(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_105])])).
% 0.38/0.60  cnf(c_0_109, negated_conjecture, (k4_tarski(k1_mcart_1(esk11_0),k2_mcart_1(esk11_0))=esk11_0), inference(rw,[status(thm)],[c_0_101, c_0_106])).
% 0.38/0.60  cnf(c_0_110, negated_conjecture, (m1_subset_1(k2_mcart_1(esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_48, c_0_107])).
% 0.38/0.60  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_110])]), c_0_73]), ['proof']).
% 0.38/0.60  # SZS output end CNFRefutation
% 0.38/0.60  # Proof object total steps             : 112
% 0.38/0.60  # Proof object clause steps            : 77
% 0.38/0.60  # Proof object formula steps           : 35
% 0.38/0.60  # Proof object conjectures             : 42
% 0.38/0.60  # Proof object clause conjectures      : 39
% 0.38/0.60  # Proof object formula conjectures     : 3
% 0.38/0.60  # Proof object initial clauses used    : 29
% 0.38/0.60  # Proof object initial formulas used   : 17
% 0.38/0.60  # Proof object generating inferences   : 32
% 0.38/0.60  # Proof object simplifying inferences  : 43
% 0.38/0.60  # Training examples: 0 positive, 0 negative
% 0.38/0.60  # Parsed axioms                        : 24
% 0.38/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.60  # Initial clauses                      : 47
% 0.38/0.60  # Removed in clause preprocessing      : 4
% 0.38/0.60  # Initial clauses in saturation        : 43
% 0.38/0.60  # Processed clauses                    : 828
% 0.38/0.60  # ...of these trivial                  : 27
% 0.38/0.60  # ...subsumed                          : 282
% 0.38/0.60  # ...remaining for further processing  : 519
% 0.38/0.60  # Other redundant clauses eliminated   : 95
% 0.38/0.60  # Clauses deleted for lack of memory   : 0
% 0.38/0.60  # Backward-subsumed                    : 16
% 0.38/0.60  # Backward-rewritten                   : 20
% 0.38/0.60  # Generated clauses                    : 26648
% 0.38/0.60  # ...of the previous two non-trivial   : 23764
% 0.38/0.60  # Contextual simplify-reflections      : 5
% 0.38/0.60  # Paramodulations                      : 26367
% 0.38/0.60  # Factorizations                       : 186
% 0.38/0.60  # Equation resolutions                 : 95
% 0.38/0.60  # Propositional unsat checks           : 0
% 0.38/0.60  #    Propositional check models        : 0
% 0.38/0.60  #    Propositional check unsatisfiable : 0
% 0.38/0.60  #    Propositional clauses             : 0
% 0.38/0.60  #    Propositional clauses after purity: 0
% 0.38/0.60  #    Propositional unsat core size     : 0
% 0.38/0.60  #    Propositional preprocessing time  : 0.000
% 0.38/0.60  #    Propositional encoding time       : 0.000
% 0.38/0.60  #    Propositional solver time         : 0.000
% 0.38/0.60  #    Success case prop preproc time    : 0.000
% 0.38/0.60  #    Success case prop encoding time   : 0.000
% 0.38/0.60  #    Success case prop solver time     : 0.000
% 0.38/0.60  # Current number of processed clauses  : 435
% 0.38/0.60  #    Positive orientable unit clauses  : 110
% 0.38/0.60  #    Positive unorientable unit clauses: 0
% 0.38/0.60  #    Negative unit clauses             : 6
% 0.38/0.60  #    Non-unit-clauses                  : 319
% 0.38/0.60  # Current number of unprocessed clauses: 21580
% 0.38/0.60  # ...number of literals in the above   : 108162
% 0.38/0.60  # Current number of archived formulas  : 0
% 0.38/0.60  # Current number of archived clauses   : 82
% 0.38/0.60  # Clause-clause subsumption calls (NU) : 14368
% 0.38/0.60  # Rec. Clause-clause subsumption calls : 11673
% 0.38/0.60  # Non-unit clause-clause subsumptions  : 301
% 0.38/0.60  # Unit Clause-clause subsumption calls : 1414
% 0.38/0.60  # Rewrite failures with RHS unbound    : 0
% 0.38/0.60  # BW rewrite match attempts            : 79
% 0.38/0.60  # BW rewrite match successes           : 13
% 0.38/0.60  # Condensation attempts                : 0
% 0.38/0.60  # Condensation successes               : 0
% 0.38/0.60  # Termbank termtop insertions          : 354575
% 0.38/0.60  
% 0.38/0.60  # -------------------------------------------------
% 0.38/0.60  # User time                : 0.246 s
% 0.38/0.60  # System time              : 0.020 s
% 0.38/0.60  # Total time               : 0.266 s
% 0.38/0.60  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
