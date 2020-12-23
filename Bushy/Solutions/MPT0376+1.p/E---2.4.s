%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t58_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:25 EDT 2019

% Result     : Theorem 264.50s
% Output     : CNFRefutation 264.50s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 210 expanded)
%              Number of clauses        :   32 (  92 expanded)
%              Number of leaves         :    7 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 900 expanded)
%              Number of equality atoms :   67 ( 148 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d1_zfmisc_1)).

fof(t58_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,X1)
     => ! [X3] :
          ( m1_subset_1(X3,X1)
         => ! [X4] :
              ( m1_subset_1(X4,X1)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( X1 != k1_xboole_0
                   => m1_subset_1(k2_enumset1(X2,X3,X4,X5),k1_zfmisc_1(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',t58_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',t7_boole)).

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d2_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',d3_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t58_subset_1.p',t6_boole)).

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X16,X15)
        | r1_tarski(X16,X14)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r1_tarski(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k1_zfmisc_1(X14) )
      & ( ~ r2_hidden(esk6_2(X18,X19),X19)
        | ~ r1_tarski(esk6_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) )
      & ( r2_hidden(esk6_2(X18,X19),X19)
        | r1_tarski(esk6_2(X18,X19),X18)
        | X19 = k1_zfmisc_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,X1)
       => ! [X3] :
            ( m1_subset_1(X3,X1)
           => ! [X4] :
                ( m1_subset_1(X4,X1)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( X1 != k1_xboole_0
                     => m1_subset_1(k2_enumset1(X2,X3,X4,X5),k1_zfmisc_1(X1)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_subset_1])).

fof(c_0_9,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X35,X34)
        | r2_hidden(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ r2_hidden(X35,X34)
        | m1_subset_1(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ m1_subset_1(X35,X34)
        | v1_xboole_0(X35)
        | ~ v1_xboole_0(X34) )
      & ( ~ v1_xboole_0(X35)
        | m1_subset_1(X35,X34)
        | ~ v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_10,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | ~ v1_xboole_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X21
        | X26 = X22
        | X26 = X23
        | X26 = X24
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X21
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X22
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k2_enumset1(X21,X22,X23,X24) )
      & ( esk7_5(X28,X29,X30,X31,X32) != X28
        | ~ r2_hidden(esk7_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( esk7_5(X28,X29,X30,X31,X32) != X29
        | ~ r2_hidden(esk7_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( esk7_5(X28,X29,X30,X31,X32) != X30
        | ~ r2_hidden(esk7_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( esk7_5(X28,X29,X30,X31,X32) != X31
        | ~ r2_hidden(esk7_5(X28,X29,X30,X31,X32),X32)
        | X32 = k2_enumset1(X28,X29,X30,X31) )
      & ( r2_hidden(esk7_5(X28,X29,X30,X31,X32),X32)
        | esk7_5(X28,X29,X30,X31,X32) = X28
        | esk7_5(X28,X29,X30,X31,X32) = X29
        | esk7_5(X28,X29,X30,X31,X32) = X30
        | esk7_5(X28,X29,X30,X31,X32) = X31
        | X32 = k2_enumset1(X28,X29,X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( ( ~ r1_tarski(X36,X37)
        | ~ r2_hidden(X38,X36)
        | r2_hidden(X38,X37) )
      & ( r2_hidden(esk8_2(X39,X40),X39)
        | r1_tarski(X39,X40) )
      & ( ~ r2_hidden(esk8_2(X39,X40),X40)
        | r1_tarski(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,esk1_0)
    & m1_subset_1(esk4_0,esk1_0)
    & m1_subset_1(esk5_0,esk1_0)
    & esk1_0 != k1_xboole_0
    & ~ m1_subset_1(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X44] :
      ( ~ v1_xboole_0(X44)
      | X44 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_subset_1(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,k2_enumset1(X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | r2_hidden(esk5_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk8_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( esk8_2(k2_enumset1(X1,X2,X3,X4),X5) = X1
    | esk8_2(k2_enumset1(X1,X2,X3,X4),X5) = X2
    | esk8_2(k2_enumset1(X1,X2,X3,X4),X5) = X3
    | esk8_2(k2_enumset1(X1,X2,X3,X4),X5) = X4
    | r2_hidden(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X5)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk8_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk5_0
    | esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk4_0
    | esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk3_0
    | esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk2_0
    | esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk3_0
    | esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_36]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk3_0
    | esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_38]),c_0_39])]),c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_40]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( esk8_2(k2_enumset1(esk2_0,esk3_0,esk4_0,esk5_0),esk1_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_41]),c_0_42])]),c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_43]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_44]),c_0_45])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
