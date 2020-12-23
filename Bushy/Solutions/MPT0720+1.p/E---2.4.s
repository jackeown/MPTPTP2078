%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t175_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:20 EDT 2019

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 296 expanded)
%              Number of clauses        :   33 ( 114 expanded)
%              Number of leaves         :    8 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 (1551 expanded)
%              Number of equality atoms :   26 ( 162 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',d4_funct_1)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',d20_funct_1)).

fof(t175_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & v5_funct_1(X2,X1) )
         => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',t175_funct_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',t7_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',d3_tarski)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',dt_o_0_0_xboole_0)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t175_funct_1.p',antisymmetry_r2_hidden)).

fof(c_0_8,plain,(
    ! [X18,X19,X20] :
      ( ( X20 != k1_funct_1(X18,X19)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X18)
        | X20 = k1_funct_1(X18,X19)
        | ~ r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 != k1_funct_1(X18,X19)
        | X20 = k1_xboole_0
        | r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 != k1_xboole_0
        | X20 = k1_funct_1(X18,X19)
        | r2_hidden(X19,k1_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v5_funct_1(X9,X8)
        | ~ r2_hidden(X10,k1_relat_1(X9))
        | r2_hidden(k1_funct_1(X9,X10),k1_funct_1(X8,X10))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk3_2(X8,X9),k1_relat_1(X9))
        | v5_funct_1(X9,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( ~ r2_hidden(k1_funct_1(X9,esk3_2(X8,X9)),k1_funct_1(X8,esk3_2(X8,X9)))
        | v5_funct_1(X9,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_funct_1(X2,X1) )
           => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_1])).

cnf(c_0_12,plain,
    ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))
    | ~ v5_funct_1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v5_funct_1(esk2_0,esk1_0)
    & ~ r1_tarski(k1_relat_1(esk2_0),k1_relat_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X35] :
      ( ~ v1_xboole_0(X35)
      | X35 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_16,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | ~ v1_xboole_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_17,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X3,X2))
    | ~ v5_funct_1(X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v5_funct_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X12,X13,X14,X15,X16] :
      ( ( ~ r1_tarski(X12,X13)
        | ~ r2_hidden(X14,X12)
        | r2_hidden(X14,X13) )
      & ( r2_hidden(esk4_2(X15,X16),X15)
        | r1_tarski(X15,X16) )
      & ( ~ r2_hidden(esk4_2(X15,X16),X16)
        | r1_tarski(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk2_0,X1),k1_funct_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(k1_funct_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k1_funct_1(X1,esk4_2(X2,k1_relat_1(X1))) = k1_xboole_0
    | r1_tarski(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_13])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_36,plain,
    ( X2 = k1_funct_1(X3,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk4_2(k1_relat_1(X1),X2),k1_funct_1(X1,esk4_2(k1_relat_1(X1),X2))),X1)
    | r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_2(X1,k1_relat_1(esk1_0))) = k1_xboole_0
    | r1_tarski(X1,k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_19]),c_0_21])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk2_0),k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,plain,
    ( r2_hidden(k1_funct_1(X1,esk4_2(k1_relat_1(X1),X2)),k1_funct_1(X3,esk4_2(k1_relat_1(X1),X2)))
    | r1_tarski(k1_relat_1(X1),X2)
    | ~ v5_funct_1(X1,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_32])).

cnf(c_0_41,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | X3 = k1_funct_1(X1,X2)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(k1_relat_1(esk2_0),k1_relat_1(esk1_0)),k1_xboole_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_20]),c_0_22])]),c_0_39])).

fof(c_0_43,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ r2_hidden(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,esk4_2(k1_relat_1(esk2_0),X1)),k1_funct_1(esk1_0,esk4_2(k1_relat_1(esk2_0),X1)))
    | r1_tarski(k1_relat_1(esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_2(k1_relat_1(esk2_0),k1_relat_1(esk1_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_20]),c_0_22])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_34]),c_0_45]),c_0_19]),c_0_21])]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_47])]),
    [proof]).
%------------------------------------------------------------------------------
