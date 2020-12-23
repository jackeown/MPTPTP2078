%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:09 EST 2020

% Result     : Theorem 54.58s
% Output     : CNFRefutation 54.58s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 345 expanded)
%              Number of clauses        :   60 ( 154 expanded)
%              Number of leaves         :   15 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  262 (1519 expanded)
%              Number of equality atoms :  108 ( 783 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(dt_k5_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(t23_mcart_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,X2)
       => X1 = k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t10_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
     => ( r2_hidden(k1_mcart_1(X1),X2)
        & r2_hidden(k2_mcart_1(X1),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(dt_k6_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

fof(dt_k7_mcart_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
     => m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

fof(d3_mcart_1,axiom,(
    ! [X1,X2,X3] : k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X46,X47,X48,X49] :
      ( ~ m1_subset_1(X49,k3_zfmisc_1(X46,X47,X48))
      | m1_subset_1(k5_mcart_1(X46,X47,X48,X49),X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).

fof(c_0_17,plain,(
    ! [X39,X40,X41] : k3_zfmisc_1(X39,X40,X41) = k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

fof(c_0_18,negated_conjecture,(
    ! [X82,X83,X84] :
      ( m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0))
      & ( ~ m1_subset_1(X82,esk8_0)
        | ~ m1_subset_1(X83,esk9_0)
        | ~ m1_subset_1(X84,esk10_0)
        | esk12_0 != k3_mcart_1(X82,X83,X84)
        | esk11_0 = X82 )
      & esk8_0 != k1_xboole_0
      & esk9_0 != k1_xboole_0
      & esk10_0 != k1_xboole_0
      & esk11_0 != k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_20])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X63,X65,X66,X67,X68] :
      ( ( r2_hidden(esk7_1(X63),X63)
        | X63 = k1_xboole_0 )
      & ( ~ r2_hidden(X65,X63)
        | esk7_1(X63) != k4_mcart_1(X65,X66,X67,X68)
        | X63 = k1_xboole_0 )
      & ( ~ r2_hidden(X66,X63)
        | esk7_1(X63) != k4_mcart_1(X65,X66,X67,X68)
        | X63 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_27,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_xboole_0(X9)
        | ~ r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_1(X11),X11)
        | v1_xboole_0(X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0)
    | v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk7_1(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk7_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( esk10_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_1(esk9_0)),k2_zfmisc_1(X2,esk9_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_1(esk10_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_32])).

cnf(c_0_46,plain,
    ( r2_hidden(esk7_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk7_1(esk9_0)),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk7_1(esk10_0)),k2_zfmisc_1(X2,esk10_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk7_1(k2_zfmisc_1(esk8_0,esk9_0)),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_51,plain,(
    ! [X69,X70,X71,X72] :
      ( ( k5_mcart_1(X69,X70,X71,X72) = k1_mcart_1(k1_mcart_1(X72))
        | ~ m1_subset_1(X72,k3_zfmisc_1(X69,X70,X71))
        | X69 = k1_xboole_0
        | X70 = k1_xboole_0
        | X71 = k1_xboole_0 )
      & ( k6_mcart_1(X69,X70,X71,X72) = k2_mcart_1(k1_mcart_1(X72))
        | ~ m1_subset_1(X72,k3_zfmisc_1(X69,X70,X71))
        | X69 = k1_xboole_0
        | X70 = k1_xboole_0
        | X71 = k1_xboole_0 )
      & ( k7_mcart_1(X69,X70,X71,X72) = k2_mcart_1(X72)
        | ~ m1_subset_1(X72,k3_zfmisc_1(X69,X70,X71))
        | X69 = k1_xboole_0
        | X70 = k1_xboole_0
        | X71 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_52,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X62)
      | ~ r2_hidden(X61,X62)
      | X61 = k4_tarski(k1_mcart_1(X61),k2_mcart_1(X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).

fof(c_0_53,plain,(
    ! [X34,X35] : v1_relat_1(k2_zfmisc_1(X34,X35)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_54,plain,(
    ! [X58,X59,X60] :
      ( ( r2_hidden(k1_mcart_1(X58),X59)
        | ~ r2_hidden(X58,k2_zfmisc_1(X59,X60)) )
      & ( r2_hidden(k2_mcart_1(X58),X60)
        | ~ r2_hidden(X58,k2_zfmisc_1(X59,X60)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_1(k2_zfmisc_1(esk8_0,esk9_0)),esk7_1(esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_59,plain,(
    ! [X50,X51,X52,X53] :
      ( ~ m1_subset_1(X53,k3_zfmisc_1(X50,X51,X52))
      | m1_subset_1(k6_mcart_1(X50,X51,X52,X53),X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).

fof(c_0_60,plain,(
    ! [X54,X55,X56,X57] :
      ( ~ m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))
      | m1_subset_1(k7_mcart_1(X54,X55,X56,X57),X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).

fof(c_0_61,plain,(
    ! [X36,X37,X38] : k3_mcart_1(X36,X37,X38) = k4_tarski(k4_tarski(X36,X37),X38) ),
    inference(variable_rename,[status(thm)],[d3_mcart_1])).

cnf(c_0_62,plain,
    ( X2 = k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_64,plain,
    ( r2_hidden(k1_mcart_1(X1),X2)
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_20])).

cnf(c_0_67,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_20])).

cnf(c_0_68,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( esk11_0 = X1
    | ~ m1_subset_1(X1,esk8_0)
    | ~ m1_subset_1(X2,esk9_0)
    | ~ m1_subset_1(X3,esk10_0)
    | esk12_0 != k3_mcart_1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,plain,
    ( k3_mcart_1(X1,X2,X3) = k4_tarski(k4_tarski(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( k1_mcart_1(k1_mcart_1(esk12_0)) = k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_24]),c_0_41]),c_0_31]),c_0_35])).

cnf(c_0_76,negated_conjecture,
    ( k2_mcart_1(k1_mcart_1(esk12_0)) = k6_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_24]),c_0_41]),c_0_31]),c_0_35])).

cnf(c_0_77,plain,
    ( m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_20])).

cnf(c_0_78,plain,
    ( m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)
    | ~ m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4)) ),
    inference(rw,[status(thm)],[c_0_69,c_0_20])).

cnf(c_0_79,plain,
    ( X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_20])).

cnf(c_0_80,negated_conjecture,
    ( esk11_0 = X1
    | esk12_0 != k4_tarski(k4_tarski(X1,X2),X3)
    | ~ m1_subset_1(X3,esk10_0)
    | ~ m1_subset_1(X2,esk9_0)
    | ~ m1_subset_1(X1,esk8_0) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k4_tarski(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),k6_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)) = k1_mcart_1(esk12_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(k6_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( esk11_0 != k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk10_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0) = k2_mcart_1(esk12_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_24]),c_0_41]),c_0_31]),c_0_35])).

cnf(c_0_86,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk12_0),X1) != esk12_0
    | ~ m1_subset_1(X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_29])]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( k4_tarski(k1_mcart_1(esk12_0),k2_mcart_1(esk12_0)) = esk12_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_65])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_mcart_1(esk12_0),esk10_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:25:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 54.58/54.83  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 54.58/54.83  # and selection function SelectNegativeLiterals.
% 54.58/54.83  #
% 54.58/54.83  # Preprocessing time       : 0.029 s
% 54.58/54.83  # Presaturation interreduction done
% 54.58/54.83  
% 54.58/54.83  # Proof found!
% 54.58/54.83  # SZS status Theorem
% 54.58/54.83  # SZS output start CNFRefutation
% 54.58/54.83  fof(t69_mcart_1, conjecture, ![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 54.58/54.83  fof(dt_k5_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k5_mcart_1(X1,X2,X3,X4),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 54.58/54.83  fof(d3_zfmisc_1, axiom, ![X1, X2, X3]:k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 54.58/54.83  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 54.58/54.83  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 54.58/54.83  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 54.58/54.83  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 54.58/54.83  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 54.58/54.83  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 54.58/54.83  fof(t23_mcart_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,X2)=>X1=k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 54.58/54.83  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 54.58/54.83  fof(t10_mcart_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k2_zfmisc_1(X2,X3))=>(r2_hidden(k1_mcart_1(X1),X2)&r2_hidden(k2_mcart_1(X1),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 54.58/54.83  fof(dt_k6_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k6_mcart_1(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 54.58/54.83  fof(dt_k7_mcart_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>m1_subset_1(k7_mcart_1(X1,X2,X3,X4),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 54.58/54.83  fof(d3_mcart_1, axiom, ![X1, X2, X3]:k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 54.58/54.83  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4, X5]:(m1_subset_1(X5,k3_zfmisc_1(X1,X2,X3))=>(![X6]:(m1_subset_1(X6,X1)=>![X7]:(m1_subset_1(X7,X2)=>![X8]:(m1_subset_1(X8,X3)=>(X5=k3_mcart_1(X6,X7,X8)=>X4=X6))))=>(X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k5_mcart_1(X1,X2,X3,X5))))), inference(assume_negation,[status(cth)],[t69_mcart_1])).
% 54.58/54.83  fof(c_0_16, plain, ![X46, X47, X48, X49]:(~m1_subset_1(X49,k3_zfmisc_1(X46,X47,X48))|m1_subset_1(k5_mcart_1(X46,X47,X48,X49),X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_mcart_1])])).
% 54.58/54.83  fof(c_0_17, plain, ![X39, X40, X41]:k3_zfmisc_1(X39,X40,X41)=k2_zfmisc_1(k2_zfmisc_1(X39,X40),X41), inference(variable_rename,[status(thm)],[d3_zfmisc_1])).
% 54.58/54.83  fof(c_0_18, negated_conjecture, ![X82, X83, X84]:(m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0))&((~m1_subset_1(X82,esk8_0)|(~m1_subset_1(X83,esk9_0)|(~m1_subset_1(X84,esk10_0)|(esk12_0!=k3_mcart_1(X82,X83,X84)|esk11_0=X82))))&(((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&esk10_0!=k1_xboole_0)&esk11_0!=k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])).
% 54.58/54.83  cnf(c_0_19, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 54.58/54.83  cnf(c_0_20, plain, (k3_zfmisc_1(X1,X2,X3)=k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 54.58/54.83  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk12_0,k3_zfmisc_1(esk8_0,esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 54.58/54.83  fof(c_0_22, plain, ![X32, X33]:(~m1_subset_1(X32,X33)|(v1_xboole_0(X33)|r2_hidden(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 54.58/54.83  cnf(c_0_23, plain, (m1_subset_1(k5_mcart_1(X2,X3,X4,X1),X2)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 54.58/54.83  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(rw,[status(thm)],[c_0_21, c_0_20])).
% 54.58/54.83  fof(c_0_25, plain, ![X13, X14, X15, X16, X19, X20, X21, X22, X23, X24, X26, X27]:(((((r2_hidden(esk2_4(X13,X14,X15,X16),X13)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14))&(r2_hidden(esk3_4(X13,X14,X15,X16),X14)|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(X16=k4_tarski(esk2_4(X13,X14,X15,X16),esk3_4(X13,X14,X15,X16))|~r2_hidden(X16,X15)|X15!=k2_zfmisc_1(X13,X14)))&(~r2_hidden(X20,X13)|~r2_hidden(X21,X14)|X19!=k4_tarski(X20,X21)|r2_hidden(X19,X15)|X15!=k2_zfmisc_1(X13,X14)))&((~r2_hidden(esk4_3(X22,X23,X24),X24)|(~r2_hidden(X26,X22)|~r2_hidden(X27,X23)|esk4_3(X22,X23,X24)!=k4_tarski(X26,X27))|X24=k2_zfmisc_1(X22,X23))&(((r2_hidden(esk5_3(X22,X23,X24),X22)|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))&(r2_hidden(esk6_3(X22,X23,X24),X23)|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23)))&(esk4_3(X22,X23,X24)=k4_tarski(esk5_3(X22,X23,X24),esk6_3(X22,X23,X24))|r2_hidden(esk4_3(X22,X23,X24),X24)|X24=k2_zfmisc_1(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 54.58/54.83  fof(c_0_26, plain, ![X63, X65, X66, X67, X68]:((r2_hidden(esk7_1(X63),X63)|X63=k1_xboole_0)&((~r2_hidden(X65,X63)|esk7_1(X63)!=k4_mcart_1(X65,X66,X67,X68)|X63=k1_xboole_0)&(~r2_hidden(X66,X63)|esk7_1(X63)!=k4_mcart_1(X65,X66,X67,X68)|X63=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 54.58/54.83  fof(c_0_27, plain, ![X9, X10, X11]:((~v1_xboole_0(X9)|~r2_hidden(X10,X9))&(r2_hidden(esk1_1(X11),X11)|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 54.58/54.83  cnf(c_0_28, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 54.58/54.83  cnf(c_0_29, negated_conjecture, (m1_subset_1(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 54.58/54.83  cnf(c_0_30, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 54.58/54.83  cnf(c_0_31, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 54.58/54.83  cnf(c_0_32, plain, (r2_hidden(esk7_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 54.58/54.83  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 54.58/54.83  cnf(c_0_34, negated_conjecture, (r2_hidden(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0)|v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 54.58/54.83  cnf(c_0_35, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 54.58/54.83  cnf(c_0_36, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 54.58/54.83  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 54.58/54.83  cnf(c_0_38, negated_conjecture, (r2_hidden(esk7_1(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 54.58/54.83  cnf(c_0_39, negated_conjecture, (r2_hidden(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 54.58/54.83  cnf(c_0_40, negated_conjecture, (r2_hidden(esk7_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 54.58/54.83  cnf(c_0_41, negated_conjecture, (esk10_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 54.58/54.83  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_36])).
% 54.58/54.83  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_1(esk9_0)),k2_zfmisc_1(X2,esk9_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 54.58/54.83  cnf(c_0_44, negated_conjecture, (r2_hidden(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk8_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 54.58/54.83  cnf(c_0_45, negated_conjecture, (r2_hidden(esk7_1(esk10_0),esk10_0)), inference(spm,[status(thm)],[c_0_41, c_0_32])).
% 54.58/54.83  cnf(c_0_46, plain, (r2_hidden(esk7_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_42, c_0_32])).
% 54.58/54.83  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk7_1(esk9_0)),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 54.58/54.83  cnf(c_0_48, negated_conjecture, (r2_hidden(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))|v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_28, c_0_24])).
% 54.58/54.83  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(X1,esk7_1(esk10_0)),k2_zfmisc_1(X2,esk10_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_45])).
% 54.58/54.83  cnf(c_0_50, negated_conjecture, (r2_hidden(esk7_1(k2_zfmisc_1(esk8_0,esk9_0)),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 54.58/54.83  fof(c_0_51, plain, ![X69, X70, X71, X72]:(((k5_mcart_1(X69,X70,X71,X72)=k1_mcart_1(k1_mcart_1(X72))|~m1_subset_1(X72,k3_zfmisc_1(X69,X70,X71))|(X69=k1_xboole_0|X70=k1_xboole_0|X71=k1_xboole_0))&(k6_mcart_1(X69,X70,X71,X72)=k2_mcart_1(k1_mcart_1(X72))|~m1_subset_1(X72,k3_zfmisc_1(X69,X70,X71))|(X69=k1_xboole_0|X70=k1_xboole_0|X71=k1_xboole_0)))&(k7_mcart_1(X69,X70,X71,X72)=k2_mcart_1(X72)|~m1_subset_1(X72,k3_zfmisc_1(X69,X70,X71))|(X69=k1_xboole_0|X70=k1_xboole_0|X71=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 54.58/54.83  fof(c_0_52, plain, ![X61, X62]:(~v1_relat_1(X62)|(~r2_hidden(X61,X62)|X61=k4_tarski(k1_mcart_1(X61),k2_mcart_1(X61)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_mcart_1])])).
% 54.58/54.83  fof(c_0_53, plain, ![X34, X35]:v1_relat_1(k2_zfmisc_1(X34,X35)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 54.58/54.83  fof(c_0_54, plain, ![X58, X59, X60]:((r2_hidden(k1_mcart_1(X58),X59)|~r2_hidden(X58,k2_zfmisc_1(X59,X60)))&(r2_hidden(k2_mcart_1(X58),X60)|~r2_hidden(X58,k2_zfmisc_1(X59,X60)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_mcart_1])])])).
% 54.58/54.83  cnf(c_0_55, negated_conjecture, (r2_hidden(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))|~r2_hidden(X1,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_33, c_0_48])).
% 54.58/54.83  cnf(c_0_56, negated_conjecture, (r2_hidden(k4_tarski(esk7_1(k2_zfmisc_1(esk8_0,esk9_0)),esk7_1(esk10_0)),k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 54.58/54.83  cnf(c_0_57, plain, (k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 54.58/54.83  cnf(c_0_58, plain, (k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 54.58/54.83  fof(c_0_59, plain, ![X50, X51, X52, X53]:(~m1_subset_1(X53,k3_zfmisc_1(X50,X51,X52))|m1_subset_1(k6_mcart_1(X50,X51,X52,X53),X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k6_mcart_1])])).
% 54.58/54.83  fof(c_0_60, plain, ![X54, X55, X56, X57]:(~m1_subset_1(X57,k3_zfmisc_1(X54,X55,X56))|m1_subset_1(k7_mcart_1(X54,X55,X56,X57),X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_mcart_1])])).
% 54.58/54.83  fof(c_0_61, plain, ![X36, X37, X38]:k3_mcart_1(X36,X37,X38)=k4_tarski(k4_tarski(X36,X37),X38), inference(variable_rename,[status(thm)],[d3_mcart_1])).
% 54.58/54.83  cnf(c_0_62, plain, (X2=k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 54.58/54.83  cnf(c_0_63, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 54.58/54.83  cnf(c_0_64, plain, (r2_hidden(k1_mcart_1(X1),X2)|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 54.58/54.83  cnf(c_0_65, negated_conjecture, (r2_hidden(esk12_0,k2_zfmisc_1(k2_zfmisc_1(esk8_0,esk9_0),esk10_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 54.58/54.83  cnf(c_0_66, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_57, c_0_20])).
% 54.58/54.83  cnf(c_0_67, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4))|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_58, c_0_20])).
% 54.58/54.83  cnf(c_0_68, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 54.58/54.83  cnf(c_0_69, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k3_zfmisc_1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 54.58/54.83  cnf(c_0_70, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 54.58/54.83  cnf(c_0_71, negated_conjecture, (esk11_0=X1|~m1_subset_1(X1,esk8_0)|~m1_subset_1(X2,esk9_0)|~m1_subset_1(X3,esk10_0)|esk12_0!=k3_mcart_1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 54.58/54.83  cnf(c_0_72, plain, (k3_mcart_1(X1,X2,X3)=k4_tarski(k4_tarski(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 54.58/54.83  cnf(c_0_73, plain, (k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1))=X1|~r2_hidden(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 54.58/54.83  cnf(c_0_74, negated_conjecture, (r2_hidden(k1_mcart_1(esk12_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 54.58/54.83  cnf(c_0_75, negated_conjecture, (k1_mcart_1(k1_mcart_1(esk12_0))=k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_24]), c_0_41]), c_0_31]), c_0_35])).
% 54.58/54.83  cnf(c_0_76, negated_conjecture, (k2_mcart_1(k1_mcart_1(esk12_0))=k6_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_24]), c_0_41]), c_0_31]), c_0_35])).
% 54.58/54.83  cnf(c_0_77, plain, (m1_subset_1(k6_mcart_1(X2,X3,X4,X1),X3)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_68, c_0_20])).
% 54.58/54.83  cnf(c_0_78, plain, (m1_subset_1(k7_mcart_1(X2,X3,X4,X1),X4)|~m1_subset_1(X1,k2_zfmisc_1(k2_zfmisc_1(X2,X3),X4))), inference(rw,[status(thm)],[c_0_69, c_0_20])).
% 54.58/54.84  cnf(c_0_79, plain, (X3=k1_xboole_0|X2=k1_xboole_0|X1=k1_xboole_0|k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))), inference(rw,[status(thm)],[c_0_70, c_0_20])).
% 54.58/54.84  cnf(c_0_80, negated_conjecture, (esk11_0=X1|esk12_0!=k4_tarski(k4_tarski(X1,X2),X3)|~m1_subset_1(X3,esk10_0)|~m1_subset_1(X2,esk9_0)|~m1_subset_1(X1,esk8_0)), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 54.58/54.84  cnf(c_0_81, negated_conjecture, (k4_tarski(k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),k6_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0))=k1_mcart_1(esk12_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])).
% 54.58/54.84  cnf(c_0_82, negated_conjecture, (m1_subset_1(k6_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk9_0)), inference(spm,[status(thm)],[c_0_77, c_0_24])).
% 54.58/54.84  cnf(c_0_83, negated_conjecture, (esk11_0!=k5_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 54.58/54.84  cnf(c_0_84, negated_conjecture, (m1_subset_1(k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0),esk10_0)), inference(spm,[status(thm)],[c_0_78, c_0_24])).
% 54.58/54.84  cnf(c_0_85, negated_conjecture, (k7_mcart_1(esk8_0,esk9_0,esk10_0,esk12_0)=k2_mcart_1(esk12_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_24]), c_0_41]), c_0_31]), c_0_35])).
% 54.58/54.84  cnf(c_0_86, negated_conjecture, (k4_tarski(k1_mcart_1(esk12_0),X1)!=esk12_0|~m1_subset_1(X1,esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_29])]), c_0_83])).
% 54.58/54.84  cnf(c_0_87, negated_conjecture, (k4_tarski(k1_mcart_1(esk12_0),k2_mcart_1(esk12_0))=esk12_0), inference(spm,[status(thm)],[c_0_73, c_0_65])).
% 54.58/54.84  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_mcart_1(esk12_0),esk10_0)), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 54.58/54.84  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])]), ['proof']).
% 54.58/54.84  # SZS output end CNFRefutation
% 54.58/54.84  # Proof object total steps             : 90
% 54.58/54.84  # Proof object clause steps            : 60
% 54.58/54.84  # Proof object formula steps           : 30
% 54.58/54.84  # Proof object conjectures             : 37
% 54.58/54.84  # Proof object clause conjectures      : 34
% 54.58/54.84  # Proof object formula conjectures     : 3
% 54.58/54.84  # Proof object initial clauses used    : 22
% 54.58/54.84  # Proof object initial formulas used   : 15
% 54.58/54.84  # Proof object generating inferences   : 28
% 54.58/54.84  # Proof object simplifying inferences  : 28
% 54.58/54.84  # Training examples: 0 positive, 0 negative
% 54.58/54.84  # Parsed axioms                        : 18
% 54.58/54.84  # Removed by relevancy pruning/SinE    : 0
% 54.58/54.84  # Initial clauses                      : 40
% 54.58/54.84  # Removed in clause preprocessing      : 3
% 54.58/54.84  # Initial clauses in saturation        : 37
% 54.58/54.84  # Processed clauses                    : 9842
% 54.58/54.84  # ...of these trivial                  : 2358
% 54.58/54.84  # ...subsumed                          : 2320
% 54.58/54.84  # ...remaining for further processing  : 5164
% 54.58/54.84  # Other redundant clauses eliminated   : 4155
% 54.58/54.84  # Clauses deleted for lack of memory   : 23549
% 54.58/54.84  # Backward-subsumed                    : 40
% 54.58/54.84  # Backward-rewritten                   : 174
% 54.58/54.84  # Generated clauses                    : 7056504
% 54.58/54.84  # ...of the previous two non-trivial   : 6354164
% 54.58/54.84  # Contextual simplify-reflections      : 19
% 54.58/54.84  # Paramodulations                      : 7051787
% 54.58/54.84  # Factorizations                       : 562
% 54.58/54.84  # Equation resolutions                 : 4156
% 54.58/54.84  # Propositional unsat checks           : 0
% 54.58/54.84  #    Propositional check models        : 0
% 54.58/54.84  #    Propositional check unsatisfiable : 0
% 54.58/54.84  #    Propositional clauses             : 0
% 54.58/54.84  #    Propositional clauses after purity: 0
% 54.58/54.84  #    Propositional unsat core size     : 0
% 54.58/54.84  #    Propositional preprocessing time  : 0.000
% 54.58/54.84  #    Propositional encoding time       : 0.000
% 54.58/54.84  #    Propositional solver time         : 0.000
% 54.58/54.84  #    Success case prop preproc time    : 0.000
% 54.58/54.84  #    Success case prop encoding time   : 0.000
% 54.58/54.84  #    Success case prop solver time     : 0.000
% 54.58/54.84  # Current number of processed clauses  : 4905
% 54.58/54.84  #    Positive orientable unit clauses  : 2965
% 54.58/54.84  #    Positive unorientable unit clauses: 0
% 54.58/54.84  #    Negative unit clauses             : 12
% 54.58/54.84  #    Non-unit-clauses                  : 1928
% 54.58/54.84  # Current number of unprocessed clauses: 1835972
% 54.58/54.84  # ...number of literals in the above   : 4312807
% 54.58/54.84  # Current number of archived formulas  : 0
% 54.58/54.84  # Current number of archived clauses   : 254
% 54.58/54.84  # Clause-clause subsumption calls (NU) : 305830
% 54.58/54.84  # Rec. Clause-clause subsumption calls : 197162
% 54.58/54.84  # Non-unit clause-clause subsumptions  : 2233
% 54.58/54.84  # Unit Clause-clause subsumption calls : 139160
% 54.58/54.84  # Rewrite failures with RHS unbound    : 0
% 54.58/54.84  # BW rewrite match attempts            : 59612
% 54.58/54.84  # BW rewrite match successes           : 36
% 54.58/54.84  # Condensation attempts                : 0
% 54.58/54.84  # Condensation successes               : 0
% 54.58/54.84  # Termbank termtop insertions          : 149914598
% 54.66/54.93  
% 54.66/54.93  # -------------------------------------------------
% 54.66/54.93  # User time                : 53.240 s
% 54.66/54.93  # System time              : 1.256 s
% 54.66/54.93  # Total time               : 54.496 s
% 54.66/54.93  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
