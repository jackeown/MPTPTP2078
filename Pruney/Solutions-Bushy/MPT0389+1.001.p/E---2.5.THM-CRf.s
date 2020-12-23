%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:33 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 177 expanded)
%              Number of clauses        :   37 (  87 expanded)
%              Number of leaves         :    9 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  175 ( 591 expanded)
%              Number of equality atoms :   48 ( 213 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t7_setfam_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ( X1 = k1_xboole_0
        | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_9,plain,(
    ! [X34,X35,X36] :
      ( ~ r2_hidden(X34,X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(X36))
      | ~ v1_xboole_0(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_10,plain,(
    ! [X32,X33] :
      ( ( ~ m1_subset_1(X32,k1_zfmisc_1(X33))
        | r1_tarski(X32,X33) )
      & ( ~ r1_tarski(X32,X33)
        | m1_subset_1(X32,k1_zfmisc_1(X33)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => ( X1 = k1_xboole_0
          | r1_tarski(k1_setfam_1(X2),k1_setfam_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t7_setfam_1])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10,X11,X13,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X9,X10)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk1_3(X7,X8,X11),X7)
        | r2_hidden(X11,X8)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( ~ r2_hidden(X11,esk1_3(X7,X8,X11))
        | r2_hidden(X11,X8)
        | X8 != k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X7,X13),X7)
        | ~ r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( ~ r2_hidden(esk2_2(X7,X13),esk3_2(X7,X13))
        | ~ r2_hidden(esk2_2(X7,X13),X13)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( r2_hidden(esk2_2(X7,X13),X13)
        | ~ r2_hidden(X16,X7)
        | r2_hidden(esk2_2(X7,X13),X16)
        | X13 = k1_setfam_1(X7)
        | X7 = k1_xboole_0 )
      & ( X18 != k1_setfam_1(X17)
        | X18 = k1_xboole_0
        | X17 != k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | X19 = k1_setfam_1(X17)
        | X17 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_13,plain,(
    ! [X37] :
      ( ~ v1_xboole_0(X37)
      | X37 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0)
    & esk6_0 != k1_xboole_0
    & ~ r1_tarski(k1_setfam_1(esk7_0),k1_setfam_1(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_20,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(X22,X20)
        | r2_hidden(X22,X21) )
      & ( r2_hidden(esk4_2(X23,X24),X23)
        | r1_tarski(X23,X24) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | r1_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk1_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( esk6_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k1_setfam_1(esk6_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,esk7_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk7_0),k1_setfam_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k1_setfam_1(esk6_0))
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk1_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_43,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk1_3(esk6_0,k1_setfam_1(esk6_0),X1),esk7_0)
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( X1 = o_0_0_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | r2_hidden(esk4_2(k1_setfam_1(X1),X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,k1_setfam_1(esk6_0),X1),esk7_0)
    | r2_hidden(X1,k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_50,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk1_3(X1,k1_setfam_1(X1),X2)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( esk7_0 = o_0_0_xboole_0
    | r1_tarski(k1_setfam_1(esk7_0),X1)
    | r2_hidden(esk4_2(k1_setfam_1(esk7_0),X1),esk1_3(esk6_0,k1_setfam_1(esk6_0),X2))
    | r2_hidden(X2,k1_setfam_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( esk7_0 = o_0_0_xboole_0
    | r1_tarski(k1_setfam_1(esk7_0),X1)
    | r2_hidden(esk4_2(k1_setfam_1(esk7_0),X1),k1_setfam_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_30])).

cnf(c_0_53,negated_conjecture,
    ( esk7_0 = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_52]),c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_53]),c_0_19])]),
    [proof]).

%------------------------------------------------------------------------------
