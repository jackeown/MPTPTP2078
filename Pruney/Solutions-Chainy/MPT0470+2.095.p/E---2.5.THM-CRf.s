%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:08 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 521 expanded)
%              Number of clauses        :   47 ( 248 expanded)
%              Number of leaves         :    7 ( 124 expanded)
%              Depth                    :   21
%              Number of atoms          :  300 (2128 expanded)
%              Number of equality atoms :   54 ( 387 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   38 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ( r2_hidden(X8,X9)
        | ~ r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))) )
      & ( X8 != X10
        | ~ r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))) )
      & ( ~ r2_hidden(X8,X9)
        | X8 = X10
        | r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( ( ~ r1_tarski(X17,X18)
        | ~ r2_hidden(k4_tarski(X19,X20),X17)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X17)
        | r1_tarski(X17,X21)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X21)
        | r1_tarski(X17,X21)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X24,X25,X26,X27,X28,X30,X31,X32,X35] :
      ( ( r2_hidden(k4_tarski(X27,esk3_5(X24,X25,X26,X27,X28)),X24)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk3_5(X24,X25,X26,X27,X28),X28),X25)
        | ~ r2_hidden(k4_tarski(X27,X28),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X30,X32),X24)
        | ~ r2_hidden(k4_tarski(X32,X31),X25)
        | r2_hidden(k4_tarski(X30,X31),X26)
        | X26 != k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)
        | ~ r2_hidden(k4_tarski(esk4_3(X24,X25,X26),X35),X24)
        | ~ r2_hidden(k4_tarski(X35,esk5_3(X24,X25,X26)),X25)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk6_3(X24,X25,X26)),X24)
        | r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk5_3(X24,X25,X26)),X25)
        | r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)
        | X26 = k5_relat_1(X24,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_11,plain,(
    ! [X11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_13,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
      | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X6)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | ~ r1_tarski(X2,X6) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_21,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_22,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_tarski(X2,k4_xboole_0(X6,k1_tarski(k4_tarski(X4,esk3_5(X2,X3,X1,X4,X5))))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( X1 != k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X1 != k5_relat_1(k1_xboole_0,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,X1),X2)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X6)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ r1_tarski(X2,X6) ),
    inference(spm,[status(thm)],[c_0_14,c_0_31])).

cnf(c_0_35,plain,
    ( X1 != k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_36,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,k4_xboole_0(X4,k1_tarski(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1))))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_33])).

cnf(c_0_37,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_tarski(X3,k4_xboole_0(X6,k1_tarski(k4_tarski(esk3_5(X2,X3,X1,X4,X5),X5)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_34])).

cnf(c_0_38,plain,
    ( ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_39,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_26])])).

cnf(c_0_40,plain,
    ( X1 != k5_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_26])])).

cnf(c_0_41,plain,
    ( X1 = k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4)
    | r2_hidden(k4_tarski(esk4_3(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4,X1),esk5_3(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4,X1)),X1)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_38,c_0_30])).

cnf(c_0_42,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,plain,
    ( X1 = k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4)
    | X1 != k5_relat_1(X5,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,k1_tarski(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1))))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_46,plain,
    ( X1 = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | r2_hidden(k4_tarski(esk4_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1),esk5_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1)),X1)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_43])).

cnf(c_0_47,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_25]),c_0_26])])).

cnf(c_0_49,plain,
    ( X1 = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | X1 != k5_relat_1(X5,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_46])).

cnf(c_0_50,plain,
    ( k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26])])).

cnf(c_0_51,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_52,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_48]),c_0_26])])).

cnf(c_0_53,plain,
    ( k5_relat_1(X1,k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_48]),c_0_26])])).

cnf(c_0_54,negated_conjecture,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26])])).

cnf(c_0_56,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_26])])).

cnf(c_0_57,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_23])).

cnf(c_0_58,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
    | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_23])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_48]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.36/1.59  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 1.36/1.59  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.36/1.59  #
% 1.36/1.59  # Preprocessing time       : 0.028 s
% 1.36/1.59  # Presaturation interreduction done
% 1.36/1.59  
% 1.36/1.59  # Proof found!
% 1.36/1.59  # SZS status Theorem
% 1.36/1.59  # SZS output start CNFRefutation
% 1.36/1.59  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.36/1.59  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 1.36/1.59  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 1.36/1.59  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.36/1.59  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.36/1.59  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 1.36/1.59  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.36/1.59  fof(c_0_7, plain, ![X8, X9, X10]:(((r2_hidden(X8,X9)|~r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))))&(X8!=X10|~r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10)))))&(~r2_hidden(X8,X9)|X8=X10|r2_hidden(X8,k4_xboole_0(X9,k1_tarski(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 1.36/1.59  fof(c_0_8, plain, ![X17, X18, X19, X20, X21]:((~r1_tarski(X17,X18)|(~r2_hidden(k4_tarski(X19,X20),X17)|r2_hidden(k4_tarski(X19,X20),X18))|~v1_relat_1(X17))&((r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X17)|r1_tarski(X17,X21)|~v1_relat_1(X17))&(~r2_hidden(k4_tarski(esk1_2(X17,X21),esk2_2(X17,X21)),X21)|r1_tarski(X17,X21)|~v1_relat_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 1.36/1.59  fof(c_0_9, plain, ![X24, X25, X26, X27, X28, X30, X31, X32, X35]:((((r2_hidden(k4_tarski(X27,esk3_5(X24,X25,X26,X27,X28)),X24)|~r2_hidden(k4_tarski(X27,X28),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk3_5(X24,X25,X26,X27,X28),X28),X25)|~r2_hidden(k4_tarski(X27,X28),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24)))&(~r2_hidden(k4_tarski(X30,X32),X24)|~r2_hidden(k4_tarski(X32,X31),X25)|r2_hidden(k4_tarski(X30,X31),X26)|X26!=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24)))&((~r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)|(~r2_hidden(k4_tarski(esk4_3(X24,X25,X26),X35),X24)|~r2_hidden(k4_tarski(X35,esk5_3(X24,X25,X26)),X25))|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&((r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk6_3(X24,X25,X26)),X24)|r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))&(r2_hidden(k4_tarski(esk6_3(X24,X25,X26),esk5_3(X24,X25,X26)),X25)|r2_hidden(k4_tarski(esk4_3(X24,X25,X26),esk5_3(X24,X25,X26)),X26)|X26=k5_relat_1(X24,X25)|~v1_relat_1(X26)|~v1_relat_1(X25)|~v1_relat_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 1.36/1.59  fof(c_0_10, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.36/1.59  fof(c_0_11, plain, ![X11]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X11)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.36/1.59  fof(c_0_12, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 1.36/1.59  cnf(c_0_13, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.36/1.59  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.36/1.59  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.36/1.59  cnf(c_0_16, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.36/1.59  cnf(c_0_17, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.36/1.59  fof(c_0_18, negated_conjecture, (v1_relat_1(esk7_0)&(k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 1.36/1.59  cnf(c_0_19, plain, (~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X1)))), inference(er,[status(thm)],[c_0_13])).
% 1.36/1.59  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X6)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X5),X4)|~r1_tarski(X2,X6)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 1.36/1.59  fof(c_0_21, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.36/1.59  cnf(c_0_22, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 1.36/1.59  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.36/1.59  cnf(c_0_24, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_tarski(X2,k4_xboole_0(X6,k1_tarski(k4_tarski(X4,esk3_5(X2,X3,X1,X4,X5)))))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 1.36/1.59  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.36/1.59  cnf(c_0_26, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 1.36/1.59  cnf(c_0_27, plain, (X1!=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 1.36/1.59  cnf(c_0_28, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.36/1.59  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X1!=k5_relat_1(k1_xboole_0,X3)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 1.36/1.59  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.36/1.59  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.36/1.59  cnf(c_0_32, plain, (r1_tarski(k5_relat_1(k1_xboole_0,X1),X2)|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_29])).
% 1.36/1.59  cnf(c_0_33, plain, (X1=k5_relat_1(X2,X3)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_14, c_0_30])).
% 1.36/1.59  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X6)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X4,X5),X3)|~r1_tarski(X2,X6)), inference(spm,[status(thm)],[c_0_14, c_0_31])).
% 1.36/1.59  cnf(c_0_35, plain, (X1!=k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 1.36/1.59  cnf(c_0_36, plain, (X1=k5_relat_1(X2,X3)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,k4_xboole_0(X4,k1_tarski(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)))))), inference(spm,[status(thm)],[c_0_19, c_0_33])).
% 1.36/1.59  cnf(c_0_37, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_tarski(X3,k4_xboole_0(X6,k1_tarski(k4_tarski(esk3_5(X2,X3,X1,X4,X5),X5))))), inference(spm,[status(thm)],[c_0_19, c_0_34])).
% 1.36/1.59  cnf(c_0_38, plain, (~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))), inference(er,[status(thm)],[c_0_35])).
% 1.36/1.59  cnf(c_0_39, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_25]), c_0_26])])).
% 1.36/1.59  cnf(c_0_40, plain, (X1!=k5_relat_1(X2,k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_25]), c_0_26])])).
% 1.36/1.59  cnf(c_0_41, plain, (X1=k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4)|r2_hidden(k4_tarski(esk4_3(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4,X1),esk5_3(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4,X1)),X1)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X4)), inference(spm,[status(thm)],[c_0_38, c_0_30])).
% 1.36/1.59  cnf(c_0_42, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_14, c_0_39])).
% 1.36/1.59  cnf(c_0_43, plain, (r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.36/1.59  cnf(c_0_44, plain, (X1=k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4)|X1!=k5_relat_1(X5,k1_xboole_0)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X1)|~v1_relat_1(X5)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X4)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.36/1.59  cnf(c_0_45, plain, (X1=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,k4_xboole_0(X3,k1_tarski(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)))))), inference(spm,[status(thm)],[c_0_19, c_0_42])).
% 1.36/1.59  cnf(c_0_46, plain, (X1=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|r2_hidden(k4_tarski(esk4_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1),esk5_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1)),X1)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_38, c_0_43])).
% 1.36/1.59  cnf(c_0_47, plain, (k5_relat_1(X1,k1_xboole_0)=k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3),X4)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X4)), inference(er,[status(thm)],[c_0_44])).
% 1.36/1.59  cnf(c_0_48, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_25]), c_0_26])])).
% 1.36/1.59  cnf(c_0_49, plain, (X1=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|X1!=k5_relat_1(X5,k1_xboole_0)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(X1)|~v1_relat_1(X5)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_46])).
% 1.36/1.59  cnf(c_0_50, plain, (k5_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2),X3)=k1_xboole_0|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_26])])).
% 1.36/1.59  cnf(c_0_51, plain, (k5_relat_1(X1,k1_xboole_0)=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_49])).
% 1.36/1.59  cnf(c_0_52, plain, (k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2)=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_48]), c_0_26])])).
% 1.36/1.59  cnf(c_0_53, plain, (k5_relat_1(X1,k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))=k1_xboole_0|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_48]), c_0_26])])).
% 1.36/1.59  cnf(c_0_54, negated_conjecture, (k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2)=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_52, c_0_23])).
% 1.36/1.59  cnf(c_0_55, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_26])])).
% 1.36/1.59  cnf(c_0_56, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_26])])).
% 1.36/1.59  cnf(c_0_57, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_56, c_0_23])).
% 1.36/1.59  cnf(c_0_58, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.36/1.59  cnf(c_0_59, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_57, c_0_23])).
% 1.36/1.59  cnf(c_0_60, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_23])])).
% 1.36/1.59  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_48]), c_0_23])]), ['proof']).
% 1.36/1.59  # SZS output end CNFRefutation
% 1.36/1.59  # Proof object total steps             : 62
% 1.36/1.59  # Proof object clause steps            : 47
% 1.36/1.59  # Proof object formula steps           : 15
% 1.36/1.59  # Proof object conjectures             : 13
% 1.36/1.59  # Proof object clause conjectures      : 10
% 1.36/1.59  # Proof object formula conjectures     : 3
% 1.36/1.59  # Proof object initial clauses used    : 12
% 1.36/1.59  # Proof object initial formulas used   : 7
% 1.36/1.59  # Proof object generating inferences   : 34
% 1.36/1.59  # Proof object simplifying inferences  : 23
% 1.36/1.59  # Training examples: 0 positive, 0 negative
% 1.36/1.59  # Parsed axioms                        : 8
% 1.36/1.59  # Removed by relevancy pruning/SinE    : 0
% 1.36/1.59  # Initial clauses                      : 18
% 1.36/1.59  # Removed in clause preprocessing      : 0
% 1.36/1.59  # Initial clauses in saturation        : 18
% 1.36/1.59  # Processed clauses                    : 5457
% 1.36/1.59  # ...of these trivial                  : 2
% 1.36/1.59  # ...subsumed                          : 3520
% 1.36/1.59  # ...remaining for further processing  : 1935
% 1.36/1.59  # Other redundant clauses eliminated   : 3
% 1.36/1.59  # Clauses deleted for lack of memory   : 0
% 1.36/1.59  # Backward-subsumed                    : 138
% 1.36/1.59  # Backward-rewritten                   : 1
% 1.36/1.59  # Generated clauses                    : 38600
% 1.36/1.59  # ...of the previous two non-trivial   : 38442
% 1.36/1.59  # Contextual simplify-reflections      : 3
% 1.36/1.59  # Paramodulations                      : 37799
% 1.36/1.59  # Factorizations                       : 6
% 1.36/1.59  # Equation resolutions                 : 795
% 1.36/1.59  # Propositional unsat checks           : 0
% 1.36/1.59  #    Propositional check models        : 0
% 1.36/1.59  #    Propositional check unsatisfiable : 0
% 1.36/1.59  #    Propositional clauses             : 0
% 1.36/1.59  #    Propositional clauses after purity: 0
% 1.36/1.59  #    Propositional unsat core size     : 0
% 1.36/1.59  #    Propositional preprocessing time  : 0.000
% 1.36/1.60  #    Propositional encoding time       : 0.000
% 1.36/1.60  #    Propositional solver time         : 0.000
% 1.36/1.60  #    Success case prop preproc time    : 0.000
% 1.36/1.60  #    Success case prop encoding time   : 0.000
% 1.36/1.60  #    Success case prop solver time     : 0.000
% 1.36/1.60  # Current number of processed clauses  : 1777
% 1.36/1.60  #    Positive orientable unit clauses  : 5
% 1.36/1.60  #    Positive unorientable unit clauses: 0
% 1.36/1.60  #    Negative unit clauses             : 3
% 1.36/1.60  #    Non-unit-clauses                  : 1769
% 1.36/1.60  # Current number of unprocessed clauses: 32800
% 1.36/1.60  # ...number of literals in the above   : 390366
% 1.36/1.60  # Current number of archived formulas  : 0
% 1.36/1.60  # Current number of archived clauses   : 157
% 1.36/1.60  # Clause-clause subsumption calls (NU) : 964790
% 1.36/1.60  # Rec. Clause-clause subsumption calls : 74740
% 1.36/1.60  # Non-unit clause-clause subsumptions  : 3605
% 1.36/1.60  # Unit Clause-clause subsumption calls : 498
% 1.36/1.60  # Rewrite failures with RHS unbound    : 0
% 1.36/1.60  # BW rewrite match attempts            : 1
% 1.36/1.60  # BW rewrite match successes           : 1
% 1.36/1.60  # Condensation attempts                : 0
% 1.36/1.60  # Condensation successes               : 0
% 1.36/1.60  # Termbank termtop insertions          : 1330341
% 1.36/1.60  
% 1.36/1.60  # -------------------------------------------------
% 1.36/1.60  # User time                : 1.214 s
% 1.36/1.60  # System time              : 0.031 s
% 1.36/1.60  # Total time               : 1.245 s
% 1.36/1.60  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
