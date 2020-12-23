%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t138_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:50 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 120 expanded)
%              Number of clauses        :   22 (  57 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 410 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',d12_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',dt_k8_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',t56_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',t7_boole)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',cc1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',fc1_xboole_0)).

fof(t138_relat_1,conjecture,(
    ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t138_relat_1.p',t138_relat_1)).

fof(c_0_7,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X13,X9)
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | X11 != k8_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(X12,X13),X10)
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | X11 != k8_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X15,X9)
        | ~ r2_hidden(k4_tarski(X14,X15),X10)
        | r2_hidden(k4_tarski(X14,X15),X11)
        | X11 != k8_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X9,X10,X11),esk3_3(X9,X10,X11)),X11)
        | ~ r2_hidden(esk3_3(X9,X10,X11),X9)
        | ~ r2_hidden(k4_tarski(esk2_3(X9,X10,X11),esk3_3(X9,X10,X11)),X10)
        | X11 = k8_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_3(X9,X10,X11),X9)
        | r2_hidden(k4_tarski(esk2_3(X9,X10,X11),esk3_3(X9,X10,X11)),X11)
        | X11 = k8_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk2_3(X9,X10,X11),esk3_3(X9,X10,X11)),X10)
        | r2_hidden(k4_tarski(esk2_3(X9,X10,X11),esk3_3(X9,X10,X11)),X11)
        | X11 = k8_relat_1(X9,X10)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k8_relat_1(X18,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | r2_hidden(k4_tarski(esk5_1(X26),esk6_1(X26)),X26)
      | X26 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

fof(c_0_12,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),k8_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk5_1(X1),esk6_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,
    ( ~ epred3_0
  <=> ! [X2] : ~ v1_xboole_0(X2) ),
    introduced(definition)).

fof(c_0_16,plain,(
    ! [X34] :
      ( ~ v1_xboole_0(X34)
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k8_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk6_1(k8_relat_1(X1,X2)),X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10])).

cnf(c_0_19,plain,
    ( epred3_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_21,plain,
    ( ~ epred4_0
  <=> ! [X3] : ~ v1_relat_1(X3) ),
    introduced(definition)).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,
    ( ~ epred5_0
  <=> ! [X1,X4] : ~ r2_hidden(k4_tarski(X4,X1),k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_24,plain,
    ( k8_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( epred3_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( epred4_0
    | ~ v1_relat_1(X1) ),
    inference(split_equiv,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_28,plain,
    ( ~ epred5_0
    | ~ epred4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_24]),c_0_17]),c_0_15]),c_0_21]),c_0_23]),c_0_25])])).

cnf(c_0_29,plain,
    ( epred4_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,plain,
    ( ~ epred5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t138_relat_1])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_23]),c_0_30])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk2_3(X1,X2,X3),esk3_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_34,negated_conjecture,(
    k8_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_35,plain,
    ( k8_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(X1,X2,k1_xboole_0),esk3_3(X1,X2,k1_xboole_0)),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27])])).

cnf(c_0_36,negated_conjecture,
    ( k8_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_35]),c_0_27])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
