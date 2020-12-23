%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t59_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 264.41s
% Output     : CNFRefutation 264.41s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 260 expanded)
%              Number of clauses        :   36 ( 114 expanded)
%              Number of leaves         :    7 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 (1178 expanded)
%              Number of equality atoms :   82 ( 185 expanded)
%              Maximal formula depth    :   32 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d1_zfmisc_1)).

fof(t59_subset_1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',t59_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',t7_boole)).

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
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d3_enumset1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',d3_tarski)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t59_subset_1.p',t6_boole)).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X18,X17)
        | r1_tarski(X18,X16)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r1_tarski(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k1_zfmisc_1(X16) )
      & ( ~ r2_hidden(esk7_2(X20,X21),X21)
        | ~ r1_tarski(esk7_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) )
      & ( r2_hidden(esk7_2(X20,X21),X21)
        | r1_tarski(esk7_2(X20,X21),X20)
        | X21 = k1_zfmisc_1(X20) ) ) ),
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
                   => ! [X6] :
                        ( m1_subset_1(X6,X1)
                       => ( X1 != k1_xboole_0
                         => m1_subset_1(k3_enumset1(X2,X3,X4,X5,X6),k1_zfmisc_1(X1)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_subset_1])).

fof(c_0_9,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X24,X23)
        | r2_hidden(X24,X23)
        | v1_xboole_0(X23) )
      & ( ~ r2_hidden(X24,X23)
        | m1_subset_1(X24,X23)
        | v1_xboole_0(X23) )
      & ( ~ m1_subset_1(X24,X23)
        | v1_xboole_0(X24)
        | ~ v1_xboole_0(X23) )
      & ( ~ v1_xboole_0(X24)
        | m1_subset_1(X24,X23)
        | ~ v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_10,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_11,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X31,X30)
        | X31 = X25
        | X31 = X26
        | X31 = X27
        | X31 = X28
        | X31 = X29
        | X30 != k3_enumset1(X25,X26,X27,X28,X29) )
      & ( X32 != X25
        | r2_hidden(X32,X30)
        | X30 != k3_enumset1(X25,X26,X27,X28,X29) )
      & ( X32 != X26
        | r2_hidden(X32,X30)
        | X30 != k3_enumset1(X25,X26,X27,X28,X29) )
      & ( X32 != X27
        | r2_hidden(X32,X30)
        | X30 != k3_enumset1(X25,X26,X27,X28,X29) )
      & ( X32 != X28
        | r2_hidden(X32,X30)
        | X30 != k3_enumset1(X25,X26,X27,X28,X29) )
      & ( X32 != X29
        | r2_hidden(X32,X30)
        | X30 != k3_enumset1(X25,X26,X27,X28,X29) )
      & ( esk8_6(X33,X34,X35,X36,X37,X38) != X33
        | ~ r2_hidden(esk8_6(X33,X34,X35,X36,X37,X38),X38)
        | X38 = k3_enumset1(X33,X34,X35,X36,X37) )
      & ( esk8_6(X33,X34,X35,X36,X37,X38) != X34
        | ~ r2_hidden(esk8_6(X33,X34,X35,X36,X37,X38),X38)
        | X38 = k3_enumset1(X33,X34,X35,X36,X37) )
      & ( esk8_6(X33,X34,X35,X36,X37,X38) != X35
        | ~ r2_hidden(esk8_6(X33,X34,X35,X36,X37,X38),X38)
        | X38 = k3_enumset1(X33,X34,X35,X36,X37) )
      & ( esk8_6(X33,X34,X35,X36,X37,X38) != X36
        | ~ r2_hidden(esk8_6(X33,X34,X35,X36,X37,X38),X38)
        | X38 = k3_enumset1(X33,X34,X35,X36,X37) )
      & ( esk8_6(X33,X34,X35,X36,X37,X38) != X37
        | ~ r2_hidden(esk8_6(X33,X34,X35,X36,X37,X38),X38)
        | X38 = k3_enumset1(X33,X34,X35,X36,X37) )
      & ( r2_hidden(esk8_6(X33,X34,X35,X36,X37,X38),X38)
        | esk8_6(X33,X34,X35,X36,X37,X38) = X33
        | esk8_6(X33,X34,X35,X36,X37,X38) = X34
        | esk8_6(X33,X34,X35,X36,X37,X38) = X35
        | esk8_6(X33,X34,X35,X36,X37,X38) = X36
        | esk8_6(X33,X34,X35,X36,X37,X38) = X37
        | X38 = k3_enumset1(X33,X34,X35,X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ( ~ r1_tarski(X40,X41)
        | ~ r2_hidden(X42,X40)
        | r2_hidden(X42,X41) )
      & ( r2_hidden(esk9_2(X43,X44),X43)
        | r1_tarski(X43,X44) )
      & ( ~ r2_hidden(esk9_2(X43,X44),X44)
        | r1_tarski(X43,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,esk1_0)
    & m1_subset_1(esk4_0,esk1_0)
    & m1_subset_1(esk5_0,esk1_0)
    & m1_subset_1(esk6_0,esk1_0)
    & esk1_0 != k1_xboole_0
    & ~ m1_subset_1(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(esk1_0)) ),
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
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk9_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X48] :
      ( ~ v1_xboole_0(X48)
      | X48 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk6_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ m1_subset_1(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(esk1_0)) ),
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
    | X1 = X6
    | ~ r2_hidden(X1,k3_enumset1(X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(esk9_2(X1,X2),X1)
    | r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | r2_hidden(esk6_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk9_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( esk9_2(k3_enumset1(X1,X2,X3,X4,X5),X6) = X1
    | esk9_2(k3_enumset1(X1,X2,X3,X4,X5),X6) = X2
    | esk9_2(k3_enumset1(X1,X2,X3,X4,X5),X6) = X3
    | esk9_2(k3_enumset1(X1,X2,X3,X4,X5),X6) = X4
    | esk9_2(k3_enumset1(X1,X2,X3,X4,X5),X6) = X5
    | r2_hidden(k3_enumset1(X1,X2,X3,X4,X5),k1_zfmisc_1(X6)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk6_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(esk9_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk6_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk5_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk4_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk3_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(esk1_0)
    | r2_hidden(esk5_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk2_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk3_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk4_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk4_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk3_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_39]),c_0_40])]),c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_41]),c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk2_0
    | esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_42]),c_0_43])]),c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_44]),c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( esk9_2(k3_enumset1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk1_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_46])]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_47]),c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_48]),c_0_49])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
