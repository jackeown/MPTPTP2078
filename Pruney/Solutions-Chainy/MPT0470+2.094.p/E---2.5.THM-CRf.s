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
% DateTime   : Thu Dec  3 10:49:08 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 345 expanded)
%              Number of clauses        :   40 ( 157 expanded)
%              Number of leaves         :    7 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          :  250 (1286 expanded)
%              Number of equality atoms :   43 ( 218 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X16,X17)
        | ~ r2_hidden(k4_tarski(X18,X19),X16)
        | r2_hidden(k4_tarski(X18,X19),X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk1_2(X16,X20),esk2_2(X16,X20)),X16)
        | r1_tarski(X16,X20)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X16,X20),esk2_2(X16,X20)),X20)
        | r1_tarski(X16,X20)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X23,X24,X25,X26,X27,X29,X30,X31,X34] :
      ( ( r2_hidden(k4_tarski(X26,esk3_5(X23,X24,X25,X26,X27)),X23)
        | ~ r2_hidden(k4_tarski(X26,X27),X25)
        | X25 != k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk3_5(X23,X24,X25,X26,X27),X27),X24)
        | ~ r2_hidden(k4_tarski(X26,X27),X25)
        | X25 != k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(X29,X31),X23)
        | ~ r2_hidden(k4_tarski(X31,X30),X24)
        | r2_hidden(k4_tarski(X29,X30),X25)
        | X25 != k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk5_3(X23,X24,X25)),X25)
        | ~ r2_hidden(k4_tarski(esk4_3(X23,X24,X25),X34),X23)
        | ~ r2_hidden(k4_tarski(X34,esk5_3(X23,X24,X25)),X24)
        | X25 = k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk6_3(X23,X24,X25)),X23)
        | r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk5_3(X23,X24,X25)),X25)
        | X25 = k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk5_3(X23,X24,X25)),X24)
        | r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk5_3(X23,X24,X25)),X25)
        | X25 = k5_relat_1(X23,X24)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_relat_1(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_10,plain,(
    ! [X10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

fof(c_0_12,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
      | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X6)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | ~ r1_tarski(X2,X6) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_21,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_tarski(X2,k2_zfmisc_1(k4_tarski(X4,esk3_5(X2,X3,X1,X4,X5)),X6)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X1 != k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | X1 != k5_relat_1(k1_xboole_0,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,X1),X2)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,X4) ),
    inference(spm,[status(thm)],[c_0_13,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X6)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | ~ r1_tarski(X2,X6) ),
    inference(spm,[status(thm)],[c_0_13,c_0_30])).

cnf(c_0_34,plain,
    ( X1 != k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_31])).

cnf(c_0_35,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X2,k2_zfmisc_1(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_32])).

cnf(c_0_36,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ r1_tarski(X3,k2_zfmisc_1(k4_tarski(esk3_5(X2,X3,X1,X4,X5),X5),X6)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_33])).

cnf(c_0_37,plain,
    ( ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_25])])).

cnf(c_0_40,plain,
    ( X1 != k5_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_25])])).

cnf(c_0_41,plain,
    ( X1 = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | r2_hidden(k4_tarski(esk4_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1),esk5_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1)),X1)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_39])).

cnf(c_0_43,plain,
    ( X1 = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | X1 != k5_relat_1(X5,k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( X1 = k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_42])).

cnf(c_0_45,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X3))
    | ~ v1_relat_1(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_46,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_25])])).

cnf(c_0_47,plain,
    ( k5_relat_1(X1,k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_25])])).

cnf(c_0_48,plain,
    ( k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_46]),c_0_25])])).

cnf(c_0_49,negated_conjecture,
    ( k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2)) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_25])])).

cnf(c_0_51,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0
    | k5_relat_1(esk7_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk7_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_22])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_46]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:24:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.46/0.66  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.46/0.66  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.46/0.66  #
% 0.46/0.66  # Preprocessing time       : 0.028 s
% 0.46/0.66  # Presaturation interreduction done
% 0.46/0.66  
% 0.46/0.66  # Proof found!
% 0.46/0.66  # SZS status Theorem
% 0.46/0.66  # SZS output start CNFRefutation
% 0.46/0.66  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.46/0.66  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.46/0.66  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.46/0.66  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.46/0.66  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.46/0.66  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.46/0.66  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.46/0.66  fof(c_0_7, plain, ![X16, X17, X18, X19, X20]:((~r1_tarski(X16,X17)|(~r2_hidden(k4_tarski(X18,X19),X16)|r2_hidden(k4_tarski(X18,X19),X17))|~v1_relat_1(X16))&((r2_hidden(k4_tarski(esk1_2(X16,X20),esk2_2(X16,X20)),X16)|r1_tarski(X16,X20)|~v1_relat_1(X16))&(~r2_hidden(k4_tarski(esk1_2(X16,X20),esk2_2(X16,X20)),X20)|r1_tarski(X16,X20)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.46/0.66  fof(c_0_8, plain, ![X23, X24, X25, X26, X27, X29, X30, X31, X34]:((((r2_hidden(k4_tarski(X26,esk3_5(X23,X24,X25,X26,X27)),X23)|~r2_hidden(k4_tarski(X26,X27),X25)|X25!=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk3_5(X23,X24,X25,X26,X27),X27),X24)|~r2_hidden(k4_tarski(X26,X27),X25)|X25!=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23)))&(~r2_hidden(k4_tarski(X29,X31),X23)|~r2_hidden(k4_tarski(X31,X30),X24)|r2_hidden(k4_tarski(X29,X30),X25)|X25!=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23)))&((~r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk5_3(X23,X24,X25)),X25)|(~r2_hidden(k4_tarski(esk4_3(X23,X24,X25),X34),X23)|~r2_hidden(k4_tarski(X34,esk5_3(X23,X24,X25)),X24))|X25=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))&((r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk6_3(X23,X24,X25)),X23)|r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk5_3(X23,X24,X25)),X25)|X25=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))&(r2_hidden(k4_tarski(esk6_3(X23,X24,X25),esk5_3(X23,X24,X25)),X24)|r2_hidden(k4_tarski(esk4_3(X23,X24,X25),esk5_3(X23,X24,X25)),X25)|X25=k5_relat_1(X23,X24)|~v1_relat_1(X25)|~v1_relat_1(X24)|~v1_relat_1(X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.46/0.66  fof(c_0_9, plain, ![X14, X15]:(~v1_relat_1(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_relat_1(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.46/0.66  fof(c_0_10, plain, ![X10]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.46/0.66  fof(c_0_11, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.46/0.66  fof(c_0_12, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.46/0.66  cnf(c_0_13, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_15, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.46/0.66  cnf(c_0_16, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.66  fof(c_0_17, negated_conjecture, (v1_relat_1(esk7_0)&(k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.46/0.66  cnf(c_0_18, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.46/0.66  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,esk3_5(X2,X3,X4,X1,X5)),X6)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_relat_1(X4)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X5),X4)|~r1_tarski(X2,X6)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.46/0.66  fof(c_0_20, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.46/0.66  cnf(c_0_21, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.46/0.66  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.66  cnf(c_0_23, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_tarski(X2,k2_zfmisc_1(k4_tarski(X4,esk3_5(X2,X3,X1,X4,X5)),X6))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.46/0.66  cnf(c_0_24, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.66  cnf(c_0_25, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.46/0.66  cnf(c_0_26, plain, (X1!=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.46/0.66  cnf(c_0_27, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  cnf(c_0_28, plain, (r1_tarski(X1,X2)|X1!=k5_relat_1(k1_xboole_0,X3)|~v1_relat_1(X1)|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.46/0.66  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk6_3(X1,X2,X3)),X1)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_31, plain, (r1_tarski(k5_relat_1(k1_xboole_0,X1),X2)|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_28])).
% 0.46/0.66  cnf(c_0_32, plain, (X1=k5_relat_1(X2,X3)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,X4)), inference(spm,[status(thm)],[c_0_13, c_0_29])).
% 0.46/0.66  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk3_5(X1,X2,X3,X4,X5),X5),X6)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X4,X5),X3)|~r1_tarski(X2,X6)), inference(spm,[status(thm)],[c_0_13, c_0_30])).
% 0.46/0.66  cnf(c_0_34, plain, (X1!=k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3)|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X1)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)), inference(spm,[status(thm)],[c_0_23, c_0_31])).
% 0.46/0.66  cnf(c_0_35, plain, (X1=k5_relat_1(X2,X3)|r2_hidden(k4_tarski(esk4_3(X2,X3,X1),esk5_3(X2,X3,X1)),X1)|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X3)|~r1_tarski(X2,k2_zfmisc_1(k4_tarski(esk4_3(X2,X3,X1),esk6_3(X2,X3,X1)),X4))), inference(spm,[status(thm)],[c_0_18, c_0_32])).
% 0.46/0.66  cnf(c_0_36, plain, (X1!=k5_relat_1(X2,X3)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X5),X1)|~r1_tarski(X3,k2_zfmisc_1(k4_tarski(esk3_5(X2,X3,X1,X4,X5),X5),X6))), inference(spm,[status(thm)],[c_0_18, c_0_33])).
% 0.46/0.66  cnf(c_0_37, plain, (~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))|~v1_relat_1(k5_relat_1(k1_xboole_0,X1))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(k5_relat_1(k1_xboole_0,X1),X2))), inference(er,[status(thm)],[c_0_34])).
% 0.46/0.66  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk5_3(X1,X2,X3)),X2)|r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X3)|X3=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_39, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_24]), c_0_25])])).
% 0.46/0.66  cnf(c_0_40, plain, (X1!=k5_relat_1(X2,k1_xboole_0)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X4),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_25])])).
% 0.46/0.66  cnf(c_0_41, plain, (X1=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|r2_hidden(k4_tarski(esk4_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1),esk5_3(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4),X1)),X1)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.46/0.66  cnf(c_0_42, plain, (X1=k5_relat_1(k1_xboole_0,X2)|r2_hidden(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_13, c_0_39])).
% 0.46/0.66  cnf(c_0_43, plain, (X1=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|X1!=k5_relat_1(X5,k1_xboole_0)|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(X1)|~v1_relat_1(X5)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.46/0.66  cnf(c_0_44, plain, (X1=k5_relat_1(k1_xboole_0,X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,k2_zfmisc_1(k4_tarski(esk4_3(k1_xboole_0,X2,X1),esk5_3(k1_xboole_0,X2,X1)),X3))), inference(spm,[status(thm)],[c_0_18, c_0_42])).
% 0.46/0.66  cnf(c_0_45, plain, (k5_relat_1(X1,k1_xboole_0)=k5_relat_1(X2,k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X3),X4))|~v1_relat_1(k5_relat_1(k1_xboole_0,X3))|~v1_relat_1(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_43])).
% 0.46/0.66  cnf(c_0_46, plain, (k5_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_25])])).
% 0.46/0.66  cnf(c_0_47, plain, (k5_relat_1(X1,k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))=k1_xboole_0|~v1_relat_1(k5_relat_1(k5_relat_1(k1_xboole_0,X2),X3))|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_25])])).
% 0.46/0.66  cnf(c_0_48, plain, (k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2))=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_46]), c_0_25])])).
% 0.46/0.66  cnf(c_0_49, negated_conjecture, (k5_relat_1(X1,k5_relat_1(k1_xboole_0,X2))=k1_xboole_0|~v1_relat_1(k5_relat_1(k1_xboole_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_22])).
% 0.46/0.66  cnf(c_0_50, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_46]), c_0_25])])).
% 0.46/0.66  cnf(c_0_51, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0|k5_relat_1(esk7_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.66  cnf(c_0_52, negated_conjecture, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_22])).
% 0.46/0.66  cnf(c_0_53, negated_conjecture, (k5_relat_1(k1_xboole_0,esk7_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_22])])).
% 0.46/0.66  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_46]), c_0_22])]), ['proof']).
% 0.46/0.66  # SZS output end CNFRefutation
% 0.46/0.66  # Proof object total steps             : 55
% 0.46/0.66  # Proof object clause steps            : 40
% 0.46/0.66  # Proof object formula steps           : 15
% 0.46/0.66  # Proof object conjectures             : 11
% 0.46/0.66  # Proof object clause conjectures      : 8
% 0.46/0.66  # Proof object formula conjectures     : 3
% 0.46/0.66  # Proof object initial clauses used    : 12
% 0.46/0.66  # Proof object initial formulas used   : 7
% 0.46/0.66  # Proof object generating inferences   : 28
% 0.46/0.66  # Proof object simplifying inferences  : 18
% 0.46/0.66  # Training examples: 0 positive, 0 negative
% 0.46/0.66  # Parsed axioms                        : 8
% 0.46/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.66  # Initial clauses                      : 16
% 0.46/0.66  # Removed in clause preprocessing      : 0
% 0.46/0.66  # Initial clauses in saturation        : 16
% 0.46/0.66  # Processed clauses                    : 1027
% 0.46/0.66  # ...of these trivial                  : 1
% 0.46/0.66  # ...subsumed                          : 530
% 0.46/0.66  # ...remaining for further processing  : 496
% 0.46/0.66  # Other redundant clauses eliminated   : 0
% 0.46/0.66  # Clauses deleted for lack of memory   : 0
% 0.46/0.66  # Backward-subsumed                    : 42
% 0.46/0.66  # Backward-rewritten                   : 1
% 0.46/0.66  # Generated clauses                    : 5049
% 0.46/0.66  # ...of the previous two non-trivial   : 4972
% 0.46/0.66  # Contextual simplify-reflections      : 0
% 0.46/0.66  # Paramodulations                      : 4858
% 0.46/0.66  # Factorizations                       : 0
% 0.46/0.66  # Equation resolutions                 : 191
% 0.46/0.66  # Propositional unsat checks           : 0
% 0.46/0.66  #    Propositional check models        : 0
% 0.46/0.66  #    Propositional check unsatisfiable : 0
% 0.46/0.66  #    Propositional clauses             : 0
% 0.46/0.66  #    Propositional clauses after purity: 0
% 0.46/0.66  #    Propositional unsat core size     : 0
% 0.46/0.66  #    Propositional preprocessing time  : 0.000
% 0.46/0.66  #    Propositional encoding time       : 0.000
% 0.46/0.66  #    Propositional solver time         : 0.000
% 0.46/0.66  #    Success case prop preproc time    : 0.000
% 0.46/0.66  #    Success case prop encoding time   : 0.000
% 0.46/0.66  #    Success case prop solver time     : 0.000
% 0.46/0.66  # Current number of processed clauses  : 437
% 0.46/0.66  #    Positive orientable unit clauses  : 4
% 0.46/0.66  #    Positive unorientable unit clauses: 0
% 0.46/0.66  #    Negative unit clauses             : 3
% 0.46/0.66  #    Non-unit-clauses                  : 430
% 0.46/0.66  # Current number of unprocessed clauses: 3932
% 0.46/0.66  # ...number of literals in the above   : 49366
% 0.46/0.66  # Current number of archived formulas  : 0
% 0.46/0.66  # Current number of archived clauses   : 59
% 0.46/0.66  # Clause-clause subsumption calls (NU) : 92195
% 0.46/0.66  # Rec. Clause-clause subsumption calls : 14079
% 0.46/0.66  # Non-unit clause-clause subsumptions  : 564
% 0.46/0.66  # Unit Clause-clause subsumption calls : 98
% 0.46/0.66  # Rewrite failures with RHS unbound    : 0
% 0.46/0.66  # BW rewrite match attempts            : 1
% 0.46/0.66  # BW rewrite match successes           : 1
% 0.46/0.66  # Condensation attempts                : 0
% 0.46/0.66  # Condensation successes               : 0
% 0.46/0.66  # Termbank termtop insertions          : 158417
% 0.46/0.66  
% 0.46/0.66  # -------------------------------------------------
% 0.46/0.66  # User time                : 0.296 s
% 0.46/0.66  # System time              : 0.009 s
% 0.46/0.66  # Total time               : 0.305 s
% 0.46/0.66  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
