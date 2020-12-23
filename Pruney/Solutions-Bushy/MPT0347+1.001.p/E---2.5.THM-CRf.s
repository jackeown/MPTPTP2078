%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0347+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:27 EST 2020

% Result     : Theorem 0.74s
% Output     : CNFRefutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   90 (6590 expanded)
%              Number of clauses        :   77 (3227 expanded)
%              Number of leaves         :    6 (1539 expanded)
%              Depth                    :   22
%              Number of atoms          :  295 (35977 expanded)
%              Number of equality atoms :   46 (5729 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t17_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        & ~ r2_hidden(X5,X4) ) ) )
               => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_subset_1)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k4_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k4_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k4_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          & ~ r2_hidden(X5,X4) ) ) )
                 => X2 = k7_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_subset_1])).

cnf(c_0_8,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X23,X24,X25] :
      ( ( m1_subset_1(esk2_3(X23,X24,X25),X23)
        | r1_tarski(X24,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(X23)) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X24)
        | r1_tarski(X24,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(X23)) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | r1_tarski(X24,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,(
    ! [X31] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
      & ( r2_hidden(X31,esk5_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( ~ r2_hidden(X31,esk6_0)
        | ~ r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & ( ~ r2_hidden(X31,esk5_0)
        | r2_hidden(X31,esk6_0)
        | r2_hidden(X31,esk4_0)
        | ~ m1_subset_1(X31,esk3_0) )
      & esk4_0 != k7_subset_1(esk3_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | m1_subset_1(k7_subset_1(X17,X18,X19),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
      | k7_subset_1(X20,X21,X22) = k4_xboole_0(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r2_hidden(esk2_3(X4,k4_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk2_3(X1,k4_xboole_0(X2,X3),X4),X2)
    | r1_tarski(k4_xboole_0(X2,X3),X4)
    | ~ m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_21,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,X1,X2),esk5_0)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,X1,X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2)
    | ~ m1_subset_1(k4_xboole_0(X1,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,esk5_0),X2)
    | ~ m1_subset_1(k4_xboole_0(X1,esk5_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,k4_xboole_0(X1,esk5_0),X2),esk4_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,esk5_0),X1)
    | ~ m1_subset_1(k4_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_31,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),k4_xboole_0(X2,X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k4_xboole_0(esk4_0,esk5_0)
    | ~ m1_subset_1(k4_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(X1,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk6_0,esk6_0),k4_xboole_0(X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk6_0) = k4_xboole_0(esk4_0,esk5_0)
    | ~ m1_subset_1(k4_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(k4_xboole_0(esk6_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_37,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk6_0) = k4_xboole_0(esk4_0,esk5_0)
    | ~ m1_subset_1(k4_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_32])])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,k4_xboole_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_37])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk4_0,esk5_0),k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_37]),c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_44,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,X2),X3,k4_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_35])])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk1_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_41]),c_0_41])).

cnf(c_0_51,plain,
    ( X1 = k4_xboole_0(X2,X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,X1,X2),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,X1,X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_18])).

cnf(c_0_53,plain,
    ( r2_hidden(esk2_3(X1,X2,k4_xboole_0(X3,X4)),X4)
    | r1_tarski(X2,k4_xboole_0(X3,X4))
    | ~ m1_subset_1(k4_xboole_0(X3,X4),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk2_3(X1,X2,k4_xboole_0(X3,X4)),X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4) = k4_xboole_0(X1,k4_xboole_0(X2,X3))
    | r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3)
    | ~ r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X4,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk4_0,esk5_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk5_0) = k4_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk6_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_13]),c_0_32])])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_3(X1,X2,k4_xboole_0(X2,X3)),X3)
    | r1_tarski(X2,k4_xboole_0(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_13]),c_0_25])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_20]),c_0_25])).

cnf(c_0_60,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X1,k4_xboole_0(X2,X3))
    | r2_hidden(esk1_3(k4_xboole_0(X1,k4_xboole_0(X2,X3)),X2,k4_xboole_0(X1,k4_xboole_0(X2,X3))),X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_63,plain,
    ( r2_hidden(esk2_3(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)),X5),X4)
    | r1_tarski(k4_xboole_0(X2,k4_xboole_0(X3,X4)),X5)
    | ~ m1_subset_1(k4_xboole_0(X2,k4_xboole_0(X3,X4)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(X1))
    | ~ r2_hidden(esk2_3(X1,k4_xboole_0(X2,k4_xboole_0(X3,X4)),X5),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk6_0,k4_xboole_0(esk6_0,esk4_0))
    | ~ m1_subset_1(k4_xboole_0(esk6_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_32])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk6_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_32])).

cnf(c_0_66,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | ~ r2_hidden(esk1_3(X1,k4_xboole_0(X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(X1,esk4_0) = X1
    | r2_hidden(esk1_3(X1,esk4_0,X1),esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_56]),c_0_61]),c_0_61]),c_0_61]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,X1,X2),esk6_0)
    | r2_hidden(esk2_3(esk3_0,X1,X2),esk4_0)
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,X1,X2),esk5_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk5_0,X2)),X3),X2)
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(esk5_0,X2)),X3)
    | ~ m1_subset_1(k4_xboole_0(X1,k4_xboole_0(esk5_0,X2)),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,k4_xboole_0(X1,k4_xboole_0(esk5_0,X2)),X3),esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_23])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk4_0) = esk6_0
    | ~ m1_subset_1(k4_xboole_0(esk6_0,esk4_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_64]),c_0_65])])).

cnf(c_0_71,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_66,c_0_41])).

cnf(c_0_72,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,esk5_0),esk4_0) = k4_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k4_xboole_0(X1,esk6_0),X2),esk4_0)
    | r1_tarski(k4_xboole_0(X1,esk6_0),X2)
    | ~ m1_subset_1(k4_xboole_0(X1,esk6_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,k4_xboole_0(X1,esk6_0),X2),esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1)),X2),X1)
    | r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1)),X2)
    | ~ m1_subset_1(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,X1)),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_20])).

cnf(c_0_75,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_25]),c_0_32])])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(X1,esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k4_xboole_0(esk5_0,esk6_0),X1),esk4_0)
    | r1_tarski(k4_xboole_0(esk5_0,esk6_0),X1)
    | ~ m1_subset_1(k4_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_20])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 != k7_subset_1(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,X2))),X3)
    | ~ m1_subset_1(k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,X2))),k1_zfmisc_1(esk3_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk5_0,k4_xboole_0(X1,X2))),X3),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,X1),esk5_0)
    | r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_74]),c_0_56]),c_0_76]),c_0_56]),c_0_76]),c_0_56]),c_0_76]),c_0_35])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk5_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k4_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_77]),c_0_35])])).

cnf(c_0_84,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk6_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_22]),c_0_79])])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_71]),c_0_71]),c_0_35]),c_0_71])])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k4_xboole_0(esk5_0,X1)),X1)
    | r1_tarski(esk4_0,k4_xboole_0(esk5_0,X1))
    | ~ m1_subset_1(k4_xboole_0(esk5_0,X1),k1_zfmisc_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_82]),c_0_35])])).

cnf(c_0_87,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(esk4_0,k4_xboole_0(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_83]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( ~ m1_subset_1(k4_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_25]),c_0_79])]),
    [proof]).

%------------------------------------------------------------------------------
