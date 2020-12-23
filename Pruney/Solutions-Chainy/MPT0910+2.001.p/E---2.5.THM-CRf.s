%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 (5348 expanded)
%              Number of clauses        :   77 (2401 expanded)
%              Number of leaves         :   11 (1283 expanded)
%              Depth                    :   19
%              Number of atoms          :  280 (22779 expanded)
%              Number of equality atoms :  167 (10404 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

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

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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

fof(t35_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 )
    <=> k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

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
                       => X4 = X7 ) ) ) )
         => ( X1 = k1_xboole_0
            | X2 = k1_xboole_0
            | X3 = k1_xboole_0
            | X4 = k6_mcart_1(X1,X2,X3,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_mcart_1])).

fof(c_0_12,plain,(
    ! [X43,X44,X45,X46] :
      ( ( k5_mcart_1(X43,X44,X45,X46) = k1_mcart_1(k1_mcart_1(X46))
        | ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( k6_mcart_1(X43,X44,X45,X46) = k2_mcart_1(k1_mcart_1(X46))
        | ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( k7_mcart_1(X43,X44,X45,X46) = k2_mcart_1(X46)
        | ~ m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_13,plain,(
    ! [X28,X29,X30] : k3_zfmisc_1(X28,X29,X30) = k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_14,negated_conjecture,(
    ! [X54,X55,X56] :
      ( m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X54,esk6_0)
        | ~ m1_subset_1(X55,esk7_0)
        | ~ m1_subset_1(X56,esk8_0)
        | esk10_0 != k3_mcart_1(X54,X55,X56)
        | esk9_0 = X55 )
      & esk6_0 != k1_xboole_0
      & esk7_0 != k1_xboole_0
      & esk8_0 != k1_xboole_0
      & esk9_0 != k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] : k3_mcart_1(X25,X26,X27) = k4_tarski(k4_tarski(X25,X26),X27) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

fof(c_0_16,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))
      | m1_subset_1(k6_mcart_1(X31,X32,X33,X34),X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

cnf(c_0_17,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
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

cnf(c_0_21,negated_conjecture,
    ( esk9_0 = X2
    | ~ m1_subset_1(X1,esk6_0)
    | ~ m1_subset_1(X2,esk7_0)
    | ~ m1_subset_1(X3,esk8_0)
    | esk10_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( esk9_0 = X2
    | esk10_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk8_0)
    | ~ m1_subset_1(X2,esk7_0)
    | ~ m1_subset_1(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) = k2_mcart_1(k1_mcart_1(esk10_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk9_0 != k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(esk10_0)
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( esk9_0 = X1
    | v1_xboole_0(esk8_0)
    | esk10_0 != k4_tarski(k4_tarski(X2,X1),X3)
    | ~ m1_subset_1(X1,esk7_0)
    | ~ m1_subset_1(X2,esk6_0)
    | ~ r2_hidden(X3,esk8_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(esk10_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_25])])).

cnf(c_0_41,negated_conjecture,
    ( esk9_0 != k2_mcart_1(k1_mcart_1(esk10_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

fof(c_0_42,plain,(
    ! [X35,X36,X37] :
      ( ( r2_hidden(k1_mcart_1(X35),X36)
        | ~ r2_hidden(X35,k2_zfmisc_1(X36,X37)) )
      & ( r2_hidden(k2_mcart_1(X35),X37)
        | ~ r2_hidden(X35,k2_zfmisc_1(X36,X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_43,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(esk8_0)
    | k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2) != esk10_0
    | ~ m1_subset_1(X1,esk6_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

fof(c_0_46,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,k2_zfmisc_1(X11,X12))
      | k4_tarski(esk1_1(X10),esk2_1(X10)) = X10 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).

cnf(c_0_47,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | v1_xboole_0(esk8_0)
    | k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2) != esk10_0
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_32])).

fof(c_0_50,plain,(
    ! [X47,X48] :
      ( k1_mcart_1(k4_tarski(X47,X48)) = X47
      & k2_mcart_1(k4_tarski(X47,X48)) = X48 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

cnf(c_0_51,plain,
    ( k4_tarski(esk1_1(X1),esk2_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2) != esk10_0
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_49]),c_0_26])).

cnf(c_0_54,plain,
    ( r2_hidden(k2_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k4_tarski(esk1_1(esk10_0),esk2_1(esk10_0)) = esk10_0
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2) != esk10_0
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_53]),c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( esk1_1(k1_mcart_1(esk10_0)) = k1_mcart_1(k1_mcart_1(esk10_0))
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( esk1_1(esk10_0) = k1_mcart_1(esk10_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),k2_mcart_1(esk10_0)) != esk10_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( esk2_1(k1_mcart_1(esk10_0)) = k2_mcart_1(k1_mcart_1(esk10_0))
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk10_0),esk2_1(esk10_0)) = esk10_0
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( esk2_1(esk10_0) = k2_mcart_1(esk10_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( k4_tarski(esk1_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_64])).

fof(c_0_72,plain,(
    ! [X40,X41,X42] :
      ( ( X40 = k1_xboole_0
        | X41 = k1_xboole_0
        | X42 = k1_xboole_0
        | k3_zfmisc_1(X40,X41,X42) != k1_xboole_0 )
      & ( X40 != k1_xboole_0
        | k3_zfmisc_1(X40,X41,X42) = k1_xboole_0 )
      & ( X41 != k1_xboole_0
        | k3_zfmisc_1(X40,X41,X42) = k1_xboole_0 )
      & ( X42 != k1_xboole_0
        | k3_zfmisc_1(X40,X41,X42) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | k4_tarski(esk1_1(esk10_0),esk2_1(esk10_0)) = esk10_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_58])).

cnf(c_0_74,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(k1_mcart_1(esk10_0))),k2_mcart_1(esk10_0)) != esk10_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0)
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0)) = esk10_0
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | esk1_1(k1_mcart_1(esk10_0)) = k1_mcart_1(k1_mcart_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_71])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k3_zfmisc_1(X1,X2,X3) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | esk1_1(esk10_0) = k1_mcart_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | esk2_1(k1_mcart_1(esk10_0)) = k2_mcart_1(k1_mcart_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | esk2_1(esk10_0) = k2_mcart_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_73])).

cnf(c_0_84,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_78,c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | esk1_1(k1_xboole_0) = k1_mcart_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | r2_hidden(k2_mcart_1(esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_58])).

cnf(c_0_87,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(k1_mcart_1(esk10_0))) = k1_mcart_1(esk10_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( k4_tarski(esk1_1(esk10_0),k2_mcart_1(esk10_0)) = esk10_0
    | k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_83])).

cnf(c_0_89,negated_conjecture,
    ( esk1_1(k1_xboole_0) = k1_mcart_1(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),k2_mcart_1(esk10_0)) != esk10_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_64])).

cnf(c_0_92,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_80]),c_0_80]),c_0_80])).

cnf(c_0_93,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_80]),c_0_80]),c_0_80]),c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(k1_xboole_0))),k2_mcart_1(k1_xboole_0)) != k1_xboole_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_80]),c_0_80]),c_0_80])).

cnf(c_0_95,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(k1_xboole_0)),esk6_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_80])).

cnf(c_0_96,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_92]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_97,negated_conjecture,
    ( k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_93]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_98,negated_conjecture,
    ( k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_97])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_98]),c_0_26]),c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:13:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.19/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t70_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_mcart_1)).
% 0.19/0.42  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.19/0.42  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 0.19/0.42  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 0.19/0.42  fof(dt_k6_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 0.19/0.42  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.42  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.42  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 0.19/0.42  fof(l139_zfmisc_1, axiom, ![X1, X2, X3]:~((r2_hidden(X1,k2_zfmisc_1(X2,X3))&![X4, X5]:k4_tarski(X4,X5)!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 0.19/0.42  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.42  fof(t35_mcart_1, axiom, ![X1, X2, X3]:(((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)<=>k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_mcart_1)).
% 0.19/0.42  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X7))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k6_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t70_mcart_1])).
% 0.19/0.42  fof(c_0_12, plain, ![X43, X44, X45, X46]:(((k5_mcart_1(X43,X44,X45,X46)=k1_mcart_1(k1_mcart_1(X46))|~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|(X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0))&(k6_mcart_1(X43,X44,X45,X46)=k2_mcart_1(k1_mcart_1(X46))|~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|(X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0)))&(k7_mcart_1(X43,X44,X45,X46)=k2_mcart_1(X46)|~m1_subset_1(X46,k3_zfmisc_1(X43,X44,X45))|(X43=k1_xboole_0|X44=k1_xboole_0|X45=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.19/0.42  fof(c_0_13, plain, ![X28, X29, X30]:k3_zfmisc_1(X28,X29,X30)=k2_zfmisc_1(k2_zfmisc_1(X28,X29),X30), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 0.19/0.42  fof(c_0_14, negated_conjecture, ![X54, X55, X56]:(m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))&((~m1_subset_1(X54,esk6_0)|(~m1_subset_1(X55,esk7_0)|(~m1_subset_1(X56,esk8_0)|(esk10_0!=k3_mcart_1(X54,X55,X56)|esk9_0=X55))))&(((esk6_0!=k1_xboole_0&esk7_0!=k1_xboole_0)&esk8_0!=k1_xboole_0)&esk9_0!=k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.19/0.42  fof(c_0_15, plain, ![X25, X26, X27]:k3_mcart_1(X25,X26,X27)=k4_tarski(k4_tarski(X25,X26),X27), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 0.19/0.42  fof(c_0_16, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X34,k3_zfmisc_1(X31,X32,X33))|m1_subset_1(k6_mcart_1(X31,X32,X33,X34),X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).
% 0.19/0.42  cnf(c_0_17, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_18, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk10_0,k3_zfmisc_1(esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  fof(c_0_20, plain, ![X15, X16]:(((~m1_subset_1(X16,X15)|r2_hidden(X16,X15)|v1_xboole_0(X15))&(~r2_hidden(X16,X15)|m1_subset_1(X16,X15)|v1_xboole_0(X15)))&((~m1_subset_1(X16,X15)|v1_xboole_0(X16)|~v1_xboole_0(X15))&(~v1_xboole_0(X16)|m1_subset_1(X16,X15)|~v1_xboole_0(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.42  cnf(c_0_21, negated_conjecture, (esk9_0=X2|~m1_subset_1(X1,esk6_0)|~m1_subset_1(X2,esk7_0)|~m1_subset_1(X3,esk8_0)|esk10_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_22, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_23, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_24, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.42  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_27, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  fof(c_0_29, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.42  cnf(c_0_30, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (esk9_0=X2|esk10_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk8_0)|~m1_subset_1(X2,esk7_0)|~m1_subset_1(X1,esk6_0)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.42  cnf(c_0_32, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_33, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_23, c_0_18])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)=k2_mcart_1(k1_mcart_1(esk10_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (esk9_0!=k6_mcart_1(esk6_0,esk7_0,esk8_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_36, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (v1_xboole_0(esk10_0)|~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.19/0.42  cnf(c_0_38, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (esk9_0=X1|v1_xboole_0(esk8_0)|esk10_0!=k4_tarski(k4_tarski(X2,X1),X3)|~m1_subset_1(X1,esk7_0)|~m1_subset_1(X2,esk6_0)|~r2_hidden(X3,esk8_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (m1_subset_1(k2_mcart_1(k1_mcart_1(esk10_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_25])])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (esk9_0!=k2_mcart_1(k1_mcart_1(esk10_0))), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 0.19/0.42  fof(c_0_42, plain, ![X35, X36, X37]:((r2_hidden(k1_mcart_1(X35),X36)|~r2_hidden(X35,k2_zfmisc_1(X36,X37)))&(r2_hidden(k2_mcart_1(X35),X37)|~r2_hidden(X35,k2_zfmisc_1(X36,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (esk10_0=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_38, c_0_25])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (v1_xboole_0(esk8_0)|k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2)!=esk10_0|~m1_subset_1(X1,esk6_0)|~r2_hidden(X2,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.19/0.42  fof(c_0_46, plain, ![X10, X11, X12]:(~r2_hidden(X10,k2_zfmisc_1(X11,X12))|k4_tarski(esk1_1(X10),esk2_1(X10))=X10), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[l139_zfmisc_1])])])])])).
% 0.19/0.42  cnf(c_0_47, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (esk10_0=k1_xboole_0|r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (v1_xboole_0(esk6_0)|v1_xboole_0(esk8_0)|k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2)!=esk10_0|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_32])).
% 0.19/0.42  fof(c_0_50, plain, ![X47, X48]:(k1_mcart_1(k4_tarski(X47,X48))=X47&k2_mcart_1(k4_tarski(X47,X48))=X48), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.42  cnf(c_0_51, plain, (k4_tarski(esk1_1(X1),esk2_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (esk10_0=k1_xboole_0|r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (v1_xboole_0(esk6_0)|k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2)!=esk10_0|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_49]), c_0_26])).
% 0.19/0.42  cnf(c_0_54, plain, (r2_hidden(k2_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_55, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (k4_tarski(esk1_1(esk10_0),esk2_1(esk10_0))=esk10_0|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|r2_hidden(esk10_0,k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0))), inference(spm,[status(thm)],[c_0_36, c_0_44])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),X2)!=esk10_0|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_53]), c_0_28])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (esk10_0=k1_xboole_0|r2_hidden(k2_mcart_1(esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (esk1_1(k1_mcart_1(esk10_0))=k1_mcart_1(k1_mcart_1(esk10_0))|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.42  cnf(c_0_62, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.42  cnf(c_0_63, negated_conjecture, (esk1_1(esk10_0)=k1_mcart_1(esk10_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_57])).
% 0.19/0.42  cnf(c_0_64, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|r2_hidden(k1_mcart_1(esk10_0),k2_zfmisc_1(esk6_0,esk7_0))), inference(spm,[status(thm)],[c_0_47, c_0_58])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (esk10_0=k1_xboole_0|k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),k2_mcart_1(esk10_0))!=esk10_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (esk10_0=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_52])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_61])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (esk2_1(k1_mcart_1(esk10_0))=k2_mcart_1(k1_mcart_1(esk10_0))|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_56])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (k4_tarski(k1_mcart_1(esk10_0),esk2_1(esk10_0))=esk10_0|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_63])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (esk2_1(esk10_0)=k2_mcart_1(esk10_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_57])).
% 0.19/0.42  cnf(c_0_71, negated_conjecture, (k4_tarski(esk1_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)|k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_64])).
% 0.19/0.42  fof(c_0_72, plain, ![X40, X41, X42]:((X40=k1_xboole_0|X41=k1_xboole_0|X42=k1_xboole_0|k3_zfmisc_1(X40,X41,X42)!=k1_xboole_0)&(((X40!=k1_xboole_0|k3_zfmisc_1(X40,X41,X42)=k1_xboole_0)&(X41!=k1_xboole_0|k3_zfmisc_1(X40,X41,X42)=k1_xboole_0))&(X42!=k1_xboole_0|k3_zfmisc_1(X40,X41,X42)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_mcart_1])])])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|k4_tarski(esk1_1(esk10_0),esk2_1(esk10_0))=esk10_0), inference(spm,[status(thm)],[c_0_51, c_0_58])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (esk10_0=k1_xboole_0|k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(k1_mcart_1(esk10_0))),k2_mcart_1(esk10_0))!=esk10_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (k4_tarski(k1_mcart_1(esk10_0),k2_mcart_1(esk10_0))=esk10_0|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|esk1_1(k1_mcart_1(esk10_0))=k1_mcart_1(k1_mcart_1(esk10_0))), inference(spm,[status(thm)],[c_0_55, c_0_71])).
% 0.19/0.42  cnf(c_0_78, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|k3_zfmisc_1(X1,X2,X3)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|esk1_1(esk10_0)=k1_mcart_1(esk10_0)), inference(spm,[status(thm)],[c_0_55, c_0_73])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (esk10_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),esk2_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)|k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_77])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|esk2_1(k1_mcart_1(esk10_0))=k2_mcart_1(k1_mcart_1(esk10_0))), inference(spm,[status(thm)],[c_0_62, c_0_71])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|esk2_1(esk10_0)=k2_mcart_1(esk10_0)), inference(spm,[status(thm)],[c_0_62, c_0_73])).
% 0.19/0.42  cnf(c_0_84, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_78, c_0_18])).
% 0.19/0.42  cnf(c_0_85, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|esk1_1(k1_xboole_0)=k1_mcart_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_80])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|r2_hidden(k2_mcart_1(esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_54, c_0_58])).
% 0.19/0.42  cnf(c_0_87, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(esk10_0)),k2_mcart_1(k1_mcart_1(esk10_0)))=k1_mcart_1(esk10_0)|k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (k4_tarski(esk1_1(esk10_0),k2_mcart_1(esk10_0))=esk10_0|k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_83])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, (esk1_1(k1_xboole_0)=k1_mcart_1(k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.42  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(esk10_0))),k2_mcart_1(esk10_0))!=esk10_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_59, c_0_86])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(esk10_0)),esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_64])).
% 0.19/0.42  cnf(c_0_92, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0)))=k1_mcart_1(k1_xboole_0)|k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_80]), c_0_80]), c_0_80])).
% 0.19/0.42  cnf(c_0_93, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_80]), c_0_80]), c_0_80]), c_0_89])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|k4_tarski(k4_tarski(X1,k2_mcart_1(k1_mcart_1(k1_xboole_0))),k2_mcart_1(k1_xboole_0))!=k1_xboole_0|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_80]), c_0_80]), c_0_80])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0|r2_hidden(k1_mcart_1(k1_mcart_1(k1_xboole_0)),esk6_0)), inference(rw,[status(thm)],[c_0_91, c_0_80])).
% 0.19/0.42  cnf(c_0_96, negated_conjecture, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0)))=k1_mcart_1(k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_92]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.42  cnf(c_0_97, negated_conjecture, (k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_93]), c_0_26]), c_0_27]), c_0_28])).
% 0.19/0.42  cnf(c_0_98, negated_conjecture, (k2_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0),esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_97])])).
% 0.19/0.42  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_98]), c_0_26]), c_0_27]), c_0_28]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 100
% 0.19/0.42  # Proof object clause steps            : 77
% 0.19/0.42  # Proof object formula steps           : 23
% 0.19/0.42  # Proof object conjectures             : 63
% 0.19/0.42  # Proof object clause conjectures      : 60
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 20
% 0.19/0.42  # Proof object initial formulas used   : 11
% 0.19/0.42  # Proof object generating inferences   : 46
% 0.19/0.42  # Proof object simplifying inferences  : 43
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 13
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 30
% 0.19/0.42  # Removed in clause preprocessing      : 2
% 0.19/0.42  # Initial clauses in saturation        : 28
% 0.19/0.42  # Processed clauses                    : 443
% 0.19/0.42  # ...of these trivial                  : 16
% 0.19/0.42  # ...subsumed                          : 81
% 0.19/0.42  # ...remaining for further processing  : 346
% 0.19/0.42  # Other redundant clauses eliminated   : 11
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 7
% 0.19/0.42  # Backward-rewritten                   : 183
% 0.19/0.42  # Generated clauses                    : 1906
% 0.19/0.42  # ...of the previous two non-trivial   : 1896
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 1880
% 0.19/0.42  # Factorizations                       : 15
% 0.19/0.42  # Equation resolutions                 : 11
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 125
% 0.19/0.42  #    Positive orientable unit clauses  : 17
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 4
% 0.19/0.42  #    Non-unit-clauses                  : 104
% 0.19/0.42  # Current number of unprocessed clauses: 1180
% 0.19/0.42  # ...number of literals in the above   : 5325
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 220
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 3856
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2113
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 88
% 0.19/0.42  # Unit Clause-clause subsumption calls : 135
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 14
% 0.19/0.42  # BW rewrite match successes           : 14
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 37326
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.076 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.081 s
% 0.19/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
