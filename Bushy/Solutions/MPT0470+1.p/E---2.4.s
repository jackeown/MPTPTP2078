%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t62_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 100 expanded)
%              Number of clauses        :   21 (  46 expanded)
%              Number of leaves         :    6 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 411 expanded)
%              Number of equality atoms :   29 (  75 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',t7_boole)).

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
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',d8_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',cc1_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',dt_k5_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',t62_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',fc1_xboole_0)).

fof(c_0_6,plain,(
    ! [X40,X41] :
      ( ~ r2_hidden(X40,X41)
      | ~ v1_xboole_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_7,plain,(
    ! [X18,X19,X20,X21,X22,X24,X25,X26,X29] :
      ( ( r2_hidden(k4_tarski(X21,esk4_5(X18,X19,X20,X21,X22)),X18)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk4_5(X18,X19,X20,X21,X22),X22),X19)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X24,X26),X18)
        | ~ r2_hidden(k4_tarski(X26,X25),X19)
        | r2_hidden(k4_tarski(X24,X25),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | ~ r2_hidden(k4_tarski(esk5_3(X18,X19,X20),X29),X18)
        | ~ r2_hidden(k4_tarski(X29,esk6_3(X18,X19,X20)),X19)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk7_3(X18,X19,X20)),X18)
        | r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk7_3(X18,X19,X20),esk6_3(X18,X19,X20)),X19)
        | r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X44] :
      ( ~ v1_xboole_0(X44)
      | v1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk7_3(X1,X2,X3)),X1)
    | r2_hidden(k4_tarski(esk5_3(X1,X2,X3),esk6_3(X1,X2,X3)),X3)
    | X3 = k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X1 != k5_relat_1(X2,X3)
    | ~ v1_xboole_0(X3)
    | ~ r2_hidden(k4_tarski(X4,X5),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_14,plain,
    ( X1 = k5_relat_1(X2,X3)
    | r2_hidden(k4_tarski(esk5_3(X2,X3,X1),esk6_3(X2,X3,X1)),X1)
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_12]),c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k5_relat_1(X2,X3)
    | X1 != k5_relat_1(X4,X5)
    | ~ v1_xboole_0(X5)
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_16,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_relat_1(X32)
      | v1_relat_1(k5_relat_1(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_17,plain,
    ( k5_relat_1(X1,X2) = k5_relat_1(X3,X4)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X3)
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_18,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_20,plain,
    ( k5_relat_1(X1,X2) = k5_relat_1(X3,X4)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_11])).

cnf(c_0_21,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_22,plain,
    ( X1 = k5_relat_1(X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_14]),c_0_11])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0
      | k5_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k5_relat_1(X2,X3)
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( k1_xboole_0 = k5_relat_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0
    | k5_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k5_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_28,c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
