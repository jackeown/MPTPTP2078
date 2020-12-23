%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t99_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:14 EDT 2019

% Result     : Theorem 228.33s
% Output     : CNFRefutation 228.33s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 212 expanded)
%              Number of equality atoms :   28 (  50 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t99_zfmisc_1.p',d1_zfmisc_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t99_zfmisc_1.p',d4_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t99_zfmisc_1.p',d3_tarski)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t99_zfmisc_1.p',t2_tarski)).

fof(t99_zfmisc_1,conjecture,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t99_zfmisc_1.p',t99_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | r1_tarski(X17,X15)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r1_tarski(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k1_zfmisc_1(X15) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r1_tarski(esk3_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | r1_tarski(esk3_2(X19,X20),X19)
        | X20 = k1_zfmisc_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_6,plain,(
    ! [X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( r2_hidden(X30,esk5_3(X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k3_tarski(X28) )
      & ( r2_hidden(esk5_3(X28,X29,X30),X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k3_tarski(X28) )
      & ( ~ r2_hidden(X32,X33)
        | ~ r2_hidden(X33,X28)
        | r2_hidden(X32,X29)
        | X29 != k3_tarski(X28) )
      & ( ~ r2_hidden(esk6_2(X34,X35),X35)
        | ~ r2_hidden(esk6_2(X34,X35),X37)
        | ~ r2_hidden(X37,X34)
        | X35 = k3_tarski(X34) )
      & ( r2_hidden(esk6_2(X34,X35),esk7_2(X34,X35))
        | r2_hidden(esk6_2(X34,X35),X35)
        | X35 = k3_tarski(X34) )
      & ( r2_hidden(esk7_2(X34,X35),X34)
        | r2_hidden(esk6_2(X34,X35),X35)
        | X35 = k3_tarski(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( ~ r1_tarski(X22,X23)
        | ~ r2_hidden(X24,X22)
        | r2_hidden(X24,X23) )
      & ( r2_hidden(esk4_2(X25,X26),X25)
        | r1_tarski(X25,X26) )
      & ( ~ r2_hidden(esk4_2(X25,X26),X26)
        | r1_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(esk5_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(esk5_3(k1_zfmisc_1(X1),k3_tarski(k1_zfmisc_1(X1)),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,esk5_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k3_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk5_3(k1_zfmisc_1(X2),k3_tarski(k1_zfmisc_1(X2)),X3))
    | ~ r2_hidden(X3,k3_tarski(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,esk5_3(X2,k3_tarski(X2),X1))
    | ~ r2_hidden(X1,k3_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X41,X42] :
      ( ( ~ r2_hidden(esk8_2(X41,X42),X41)
        | ~ r2_hidden(esk8_2(X41,X42),X42)
        | X41 = X42 )
      & ( r2_hidden(esk8_2(X41,X42),X41)
        | r2_hidden(esk8_2(X41,X42),X42)
        | X41 = X42 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t99_zfmisc_1])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_tarski(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r2_hidden(esk8_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(esk8_2(X1,X2),X1)
    | ~ r2_hidden(esk8_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k3_tarski(k1_zfmisc_1(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,negated_conjecture,(
    k3_tarski(k1_zfmisc_1(esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk8_2(X1,k3_tarski(k1_zfmisc_1(X2))),X2)
    | X1 = k3_tarski(k1_zfmisc_1(X2))
    | r2_hidden(esk8_2(X1,k3_tarski(k1_zfmisc_1(X2))),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( X1 = k3_tarski(k1_zfmisc_1(X2))
    | ~ r2_hidden(esk8_2(X1,k3_tarski(k1_zfmisc_1(X2))),X1)
    | ~ r2_hidden(esk8_2(X1,k3_tarski(k1_zfmisc_1(X2))),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k3_tarski(k1_zfmisc_1(esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_32,c_0_33,c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
