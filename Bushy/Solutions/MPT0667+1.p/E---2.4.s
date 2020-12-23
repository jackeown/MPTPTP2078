%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t84_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:27 EDT 2019

% Result     : Theorem 264.47s
% Output     : CNFRefutation 264.47s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 289 expanded)
%              Number of clauses        :   37 ( 108 expanded)
%              Number of leaves         :    8 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  175 (1030 expanded)
%              Number of equality atoms :   40 ( 124 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => v2_funct_1(k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',t84_funct_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',t90_relat_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',d8_funct_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',commutativity_k3_xboole_0)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',fc8_funct_1)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',t70_funct_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',d4_xboole_0)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t84_funct_1.p',dt_k7_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => v2_funct_1(k7_relat_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t84_funct_1])).

fof(c_0_9,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | k1_relat_1(k7_relat_1(X44,X43)) = k3_xboole_0(k1_relat_1(X44),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ v2_funct_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v2_funct_1(X20)
        | ~ r2_hidden(X21,k1_relat_1(X20))
        | ~ r2_hidden(X22,k1_relat_1(X20))
        | k1_funct_1(X20,X21) != k1_funct_1(X20,X22)
        | X21 = X22
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk4_1(X20),k1_relat_1(X20))
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( r2_hidden(esk5_1(X20),k1_relat_1(X20))
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( k1_funct_1(X20,esk4_1(X20)) = k1_funct_1(X20,esk5_1(X20))
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( esk4_1(X20) != esk5_1(X20)
        | v2_funct_1(X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_12,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_funct_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,X1)) = k3_xboole_0(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X45,X46] :
      ( ( v1_relat_1(k7_relat_1(X45,X46))
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( v1_funct_1(k7_relat_1(X45,X46))
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_20,plain,(
    ! [X36,X37,X38] :
      ( ~ v1_relat_1(X38)
      | ~ v1_funct_1(X38)
      | ~ r2_hidden(X36,k1_relat_1(k7_relat_1(X38,X37)))
      | k1_funct_1(k7_relat_1(X38,X37),X36) = k1_funct_1(X38,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( k1_funct_1(X1,esk4_1(X1)) = k1_funct_1(X1,esk5_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk3_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk3_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X16)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk3_3(X16,X17,X18),X17)
        | r2_hidden(esk3_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_1(k7_relat_1(esk2_0,esk1_0)),k3_xboole_0(esk1_0,k1_relat_1(esk2_0)))
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_25,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_27,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | v1_relat_1(k7_relat_1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_28,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_1(k7_relat_1(esk2_0,esk1_0)),k3_xboole_0(esk1_0,k1_relat_1(esk2_0)))
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_21]),c_0_17]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk1_0),esk5_1(k7_relat_1(esk2_0,esk1_0))) = k1_funct_1(k7_relat_1(esk2_0,esk1_0),esk4_1(k7_relat_1(esk2_0,esk1_0)))
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_1(k7_relat_1(esk2_0,esk1_0)),k3_xboole_0(esk1_0,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_13])])).

cnf(c_0_33,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,X1),X2) = k1_funct_1(esk2_0,X2)
    | ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(esk2_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_26]),c_0_13])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk5_1(k7_relat_1(esk2_0,esk1_0)),k3_xboole_0(esk1_0,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_26]),c_0_13])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk1_0),esk5_1(k7_relat_1(esk2_0,esk1_0))) = k1_funct_1(k7_relat_1(esk2_0,esk1_0),esk4_1(k7_relat_1(esk2_0,esk1_0)))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_13])])).

cnf(c_0_37,plain,
    ( v2_funct_1(X1)
    | esk4_1(X1) != esk5_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_1(k7_relat_1(esk2_0,esk1_0)),k3_xboole_0(esk1_0,k1_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_13])])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,X1),X2) = k1_funct_1(esk2_0,X2)
    | ~ r2_hidden(X2,k3_xboole_0(X1,k1_relat_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_1(k7_relat_1(esk2_0,esk1_0)),k3_xboole_0(esk1_0,k1_relat_1(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_13])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk1_0),esk5_1(k7_relat_1(esk2_0,esk1_0))) = k1_funct_1(k7_relat_1(esk2_0,esk1_0),esk4_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_13])])).

cnf(c_0_43,negated_conjecture,
    ( esk5_1(k7_relat_1(esk2_0,esk1_0)) != esk4_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_funct_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_37])).

cnf(c_0_44,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_1(k7_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk1_0),esk4_1(k7_relat_1(esk2_0,esk1_0))) = k1_funct_1(esk2_0,esk5_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( esk5_1(k7_relat_1(esk2_0,esk1_0)) != esk4_1(k7_relat_1(esk2_0,esk1_0))
    | ~ v1_relat_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_26]),c_0_13])])).

cnf(c_0_49,negated_conjecture,
    ( X1 = esk4_1(k7_relat_1(esk2_0,esk1_0))
    | k1_funct_1(esk2_0,X1) != k1_funct_1(esk2_0,esk4_1(k7_relat_1(esk2_0,esk1_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_26]),c_0_13])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_1(k7_relat_1(esk2_0,esk1_0)),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_1(k7_relat_1(esk2_0,esk1_0))) = k1_funct_1(esk2_0,esk4_1(k7_relat_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( esk5_1(k7_relat_1(esk2_0,esk1_0)) != esk4_1(k7_relat_1(esk2_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_13])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
