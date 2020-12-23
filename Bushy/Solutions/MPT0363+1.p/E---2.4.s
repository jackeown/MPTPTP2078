%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t43_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:23 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 146 expanded)
%              Number of clauses        :   37 (  69 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 544 expanded)
%              Number of equality atoms :   13 (  36 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_xboole_0(X2,X3)
          <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t43_subset_1.p',t43_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t43_subset_1.p',d5_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t43_subset_1.p',t3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t43_subset_1.p',d3_tarski)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t43_subset_1.p',d5_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t43_subset_1.p',l3_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t43_subset_1.p',symmetry_r1_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_xboole_0(X2,X3)
            <=> r1_tarski(X2,k3_subset_1(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_subset_1])).

fof(c_0_8,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk5_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk5_3(X23,X24,X25),X23)
        | r2_hidden(esk5_3(X23,X24,X25),X24)
        | X25 = k4_xboole_0(X23,X24) )
      & ( r2_hidden(esk5_3(X23,X24,X25),X23)
        | r2_hidden(esk5_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) )
      & ( ~ r2_hidden(esk5_3(X23,X24,X25),X24)
        | r2_hidden(esk5_3(X23,X24,X25),X25)
        | X25 = k4_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X43,X44,X46,X47,X48] :
      ( ( r2_hidden(esk7_2(X43,X44),X43)
        | r1_xboole_0(X43,X44) )
      & ( r2_hidden(esk7_2(X43,X44),X44)
        | r1_xboole_0(X43,X44) )
      & ( ~ r2_hidden(X48,X46)
        | ~ r2_hidden(X48,X47)
        | ~ r1_xboole_0(X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_10,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk4_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk4_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | k3_subset_1(X16,X17) = k4_xboole_0(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ( ~ r1_xboole_0(esk2_0,esk3_0)
      | ~ r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)) )
    & ( r1_xboole_0(esk2_0,esk3_0)
      | r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | ~ r2_hidden(X37,X36)
      | r2_hidden(X37,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(esk7_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk7_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(esk7_2(X1,X2),X3)
    | r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    | r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( k3_subset_1(esk1_0,esk3_0) = k4_xboole_0(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_29,plain,(
    ! [X40,X41] :
      ( ~ r1_xboole_0(X40,X41)
      | r1_xboole_0(X41,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk7_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk1_0,esk3_0))
    | r1_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_39,plain,
    ( r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X3)
    | r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk4_2(X1,k4_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_2(esk2_0,X1),esk1_0)
    | r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0)
    | r1_xboole_0(X1,esk2_0)
    | ~ r1_xboole_0(k4_xboole_0(esk1_0,esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_xboole_0(esk2_0,esk3_0)
    | ~ r1_tarski(esk2_0,k3_subset_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_2(esk2_0,k4_xboole_0(esk1_0,X1)),X1)
    | r1_tarski(esk2_0,k4_xboole_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k4_xboole_0(esk1_0,esk3_0))
    | ~ r1_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk2_0,k4_xboole_0(esk1_0,X1))
    | ~ r1_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k4_xboole_0(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_46])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
