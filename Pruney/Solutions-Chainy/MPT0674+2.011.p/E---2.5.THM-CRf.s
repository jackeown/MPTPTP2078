%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:24 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 165 expanded)
%              Number of clauses        :   42 (  72 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  180 ( 506 expanded)
%              Number of equality atoms :   66 ( 161 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_10,plain,(
    ! [X27,X28] :
      ( ( r2_hidden(esk3_2(X27,X28),X27)
        | X27 = k1_tarski(X28)
        | X27 = k1_xboole_0 )
      & ( esk3_2(X27,X28) != X28
        | X27 = k1_tarski(X28)
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

fof(c_0_11,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X30,X31,X32] :
      ( ( ~ r2_hidden(k4_tarski(X30,X31),X32)
        | r2_hidden(X31,k11_relat_1(X32,X30))
        | ~ v1_relat_1(X32) )
      & ( ~ r2_hidden(X31,k11_relat_1(X32,X30))
        | r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk4_0,k1_relat_1(esk5_0))
    & k11_relat_1(esk5_0,esk4_0) != k1_tarski(k1_funct_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_23,plain,(
    ! [X14,X15,X17,X18,X19] :
      ( ( r1_xboole_0(X14,X15)
        | r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)) )
      & ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
        | ~ r1_xboole_0(X17,X18) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_24,plain,(
    ! [X20] : r1_xboole_0(X20,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_25,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_26,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,k1_relat_1(X35))
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X34 = k1_funct_1(X35,X33)
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X33,k1_relat_1(X35))
        | X34 != k1_funct_1(X35,X33)
        | r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_27,plain,
    ( k11_relat_1(X1,X2) = k2_enumset1(X3,X3,X3,X3)
    | k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk3_2(k11_relat_1(X1,X2),X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) != k1_tarski(k1_funct_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k11_relat_1(esk5_0,X1) = k2_enumset1(X2,X2,X2,X2)
    | k11_relat_1(esk5_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk3_2(k11_relat_1(esk5_0,X1),X2)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) != k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_42,negated_conjecture,
    ( esk3_2(k11_relat_1(esk5_0,X1),X2) = k1_funct_1(esk5_0,X1)
    | k11_relat_1(esk5_0,X1) = k2_enumset1(X2,X2,X2,X2)
    | k11_relat_1(esk5_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_28])])).

cnf(c_0_43,plain,
    ( X1 = k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))
    | r2_hidden(esk1_3(X2,k3_xboole_0(X3,k1_xboole_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( X1 = k3_xboole_0(X2,k3_xboole_0(X3,X4))
    | r2_hidden(esk1_3(X2,k3_xboole_0(X3,X4),X1),X1)
    | r2_hidden(esk1_3(X2,k3_xboole_0(X3,X4),X1),X4) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk3_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( esk3_2(k11_relat_1(esk5_0,X1),k1_funct_1(esk5_0,esk4_0)) = k1_funct_1(esk5_0,X1)
    | k11_relat_1(esk5_0,X1) = k1_xboole_0
    | k11_relat_1(esk5_0,X1) != k11_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

cnf(c_0_51,plain,
    ( X1 = k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))
    | r2_hidden(esk1_3(X2,k3_xboole_0(X3,k1_xboole_0),X1),k3_xboole_0(X4,X1))
    | ~ r2_hidden(esk1_3(X2,k3_xboole_0(X3,k1_xboole_0),X1),X4) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,X3)) = X3
    | r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),X3),X3) ),
    inference(ef,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk5_0,esk4_0)),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_35]),c_0_28])])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk3_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_16]),c_0_17]),c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( esk3_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)) = k1_funct_1(esk5_0,esk4_0)
    | k11_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_50])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,esk4_0),k11_relat_1(esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_28])])).

cnf(c_0_60,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_41])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_61]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.87/1.11  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.87/1.11  # and selection function SelectCQArNTNpEqFirst.
% 0.87/1.11  #
% 0.87/1.11  # Preprocessing time       : 0.027 s
% 0.87/1.11  # Presaturation interreduction done
% 0.87/1.11  
% 0.87/1.11  # Proof found!
% 0.87/1.11  # SZS status Theorem
% 0.87/1.11  # SZS output start CNFRefutation
% 0.87/1.11  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.87/1.11  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.87/1.11  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.87/1.11  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.87/1.11  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.87/1.11  fof(t117_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 0.87/1.11  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.87/1.11  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.87/1.11  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.87/1.11  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.87/1.11  fof(c_0_10, plain, ![X27, X28]:((r2_hidden(esk3_2(X27,X28),X27)|(X27=k1_tarski(X28)|X27=k1_xboole_0))&(esk3_2(X27,X28)!=X28|(X27=k1_tarski(X28)|X27=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.87/1.11  fof(c_0_11, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.87/1.11  fof(c_0_12, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.87/1.11  fof(c_0_13, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.87/1.11  fof(c_0_14, plain, ![X30, X31, X32]:((~r2_hidden(k4_tarski(X30,X31),X32)|r2_hidden(X31,k11_relat_1(X32,X30))|~v1_relat_1(X32))&(~r2_hidden(X31,k11_relat_1(X32,X30))|r2_hidden(k4_tarski(X30,X31),X32)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.87/1.11  cnf(c_0_15, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.87/1.11  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.87/1.11  cnf(c_0_17, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.87/1.11  cnf(c_0_18, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.11  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t117_funct_1])).
% 0.87/1.11  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.11  cnf(c_0_21, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])).
% 0.87/1.11  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r2_hidden(esk4_0,k1_relat_1(esk5_0))&k11_relat_1(esk5_0,esk4_0)!=k1_tarski(k1_funct_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.87/1.11  fof(c_0_23, plain, ![X14, X15, X17, X18, X19]:((r1_xboole_0(X14,X15)|r2_hidden(esk2_2(X14,X15),k3_xboole_0(X14,X15)))&(~r2_hidden(X19,k3_xboole_0(X17,X18))|~r1_xboole_0(X17,X18))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.87/1.11  fof(c_0_24, plain, ![X20]:r1_xboole_0(X20,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.87/1.11  fof(c_0_25, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.87/1.11  fof(c_0_26, plain, ![X33, X34, X35]:(((r2_hidden(X33,k1_relat_1(X35))|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(X34=k1_funct_1(X35,X33)|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X33,k1_relat_1(X35))|X34!=k1_funct_1(X35,X33)|r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.87/1.11  cnf(c_0_27, plain, (k11_relat_1(X1,X2)=k2_enumset1(X3,X3,X3,X3)|k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk3_2(k11_relat_1(X1,X2),X3)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.87/1.11  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.87/1.11  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.87/1.11  cnf(c_0_30, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.87/1.11  cnf(c_0_31, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.87/1.11  cnf(c_0_32, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)!=k1_tarski(k1_funct_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.87/1.11  cnf(c_0_33, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.11  cnf(c_0_34, negated_conjecture, (k11_relat_1(esk5_0,X1)=k2_enumset1(X2,X2,X2,X2)|k11_relat_1(esk5_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk3_2(k11_relat_1(esk5_0,X1),X2)),esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.87/1.11  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.87/1.11  cnf(c_0_36, plain, (~r2_hidden(X1,k3_xboole_0(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.87/1.11  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.87/1.11  cnf(c_0_38, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.87/1.11  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.87/1.11  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.11  cnf(c_0_41, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)!=k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_16]), c_0_17]), c_0_18])).
% 0.87/1.11  cnf(c_0_42, negated_conjecture, (esk3_2(k11_relat_1(esk5_0,X1),X2)=k1_funct_1(esk5_0,X1)|k11_relat_1(esk5_0,X1)=k2_enumset1(X2,X2,X2,X2)|k11_relat_1(esk5_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_28])])).
% 0.87/1.11  cnf(c_0_43, plain, (X1=k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))|r2_hidden(esk1_3(X2,k3_xboole_0(X3,k1_xboole_0),X1),X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.87/1.11  cnf(c_0_44, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_38])).
% 0.87/1.11  cnf(c_0_45, plain, (X1=k3_xboole_0(X2,k3_xboole_0(X3,X4))|r2_hidden(esk1_3(X2,k3_xboole_0(X3,X4),X1),X1)|r2_hidden(esk1_3(X2,k3_xboole_0(X3,X4),X1),X4)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.87/1.11  cnf(c_0_46, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_40])).
% 0.87/1.11  cnf(c_0_47, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.87/1.11  cnf(c_0_48, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk3_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.87/1.11  cnf(c_0_49, negated_conjecture, (esk3_2(k11_relat_1(esk5_0,X1),k1_funct_1(esk5_0,esk4_0))=k1_funct_1(esk5_0,X1)|k11_relat_1(esk5_0,X1)=k1_xboole_0|k11_relat_1(esk5_0,X1)!=k11_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.87/1.11  cnf(c_0_50, plain, (k3_xboole_0(X1,k1_xboole_0)=k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 0.87/1.11  cnf(c_0_51, plain, (X1=k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))|r2_hidden(esk1_3(X2,k3_xboole_0(X3,k1_xboole_0),X1),k3_xboole_0(X4,X1))|~r2_hidden(esk1_3(X2,k3_xboole_0(X3,k1_xboole_0),X1),X4)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 0.87/1.11  cnf(c_0_52, plain, (k3_xboole_0(X1,k3_xboole_0(X2,X3))=X3|r2_hidden(esk1_3(X1,k3_xboole_0(X2,X3),X3),X3)), inference(ef,[status(thm)],[c_0_45])).
% 0.87/1.11  cnf(c_0_53, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.87/1.11  cnf(c_0_54, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk5_0,esk4_0)),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_35]), c_0_28])])).
% 0.87/1.11  cnf(c_0_55, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk3_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_16]), c_0_17]), c_0_18])).
% 0.87/1.11  cnf(c_0_56, negated_conjecture, (esk3_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))=k1_funct_1(esk5_0,esk4_0)|k11_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.87/1.11  cnf(c_0_57, plain, (~r2_hidden(X1,k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_36, c_0_50])).
% 0.87/1.11  cnf(c_0_58, plain, (k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_36])).
% 0.87/1.11  cnf(c_0_59, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,esk4_0),k11_relat_1(esk5_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_28])])).
% 0.87/1.11  cnf(c_0_60, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_41])).
% 0.87/1.11  cnf(c_0_61, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.87/1.11  cnf(c_0_62, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_61]), ['proof']).
% 0.87/1.11  # SZS output end CNFRefutation
% 0.87/1.11  # Proof object total steps             : 63
% 0.87/1.11  # Proof object clause steps            : 42
% 0.87/1.11  # Proof object formula steps           : 21
% 0.87/1.11  # Proof object conjectures             : 16
% 0.87/1.11  # Proof object clause conjectures      : 13
% 0.87/1.11  # Proof object formula conjectures     : 3
% 0.87/1.11  # Proof object initial clauses used    : 18
% 0.87/1.11  # Proof object initial formulas used   : 10
% 0.87/1.11  # Proof object generating inferences   : 16
% 0.87/1.11  # Proof object simplifying inferences  : 25
% 0.87/1.11  # Training examples: 0 positive, 0 negative
% 0.87/1.11  # Parsed axioms                        : 10
% 0.87/1.11  # Removed by relevancy pruning/SinE    : 0
% 0.87/1.11  # Initial clauses                      : 23
% 0.87/1.11  # Removed in clause preprocessing      : 3
% 0.87/1.11  # Initial clauses in saturation        : 20
% 0.87/1.11  # Processed clauses                    : 6756
% 0.87/1.11  # ...of these trivial                  : 59
% 0.87/1.11  # ...subsumed                          : 4973
% 0.87/1.11  # ...remaining for further processing  : 1724
% 0.87/1.11  # Other redundant clauses eliminated   : 5
% 0.87/1.11  # Clauses deleted for lack of memory   : 0
% 0.87/1.11  # Backward-subsumed                    : 83
% 0.87/1.11  # Backward-rewritten                   : 1028
% 0.87/1.11  # Generated clauses                    : 73098
% 0.87/1.11  # ...of the previous two non-trivial   : 66645
% 0.87/1.11  # Contextual simplify-reflections      : 12
% 0.87/1.11  # Paramodulations                      : 72996
% 0.87/1.11  # Factorizations                       : 96
% 0.87/1.11  # Equation resolutions                 : 6
% 0.87/1.11  # Propositional unsat checks           : 0
% 0.87/1.11  #    Propositional check models        : 0
% 0.87/1.11  #    Propositional check unsatisfiable : 0
% 0.87/1.11  #    Propositional clauses             : 0
% 0.87/1.11  #    Propositional clauses after purity: 0
% 0.87/1.11  #    Propositional unsat core size     : 0
% 0.87/1.11  #    Propositional preprocessing time  : 0.000
% 0.87/1.11  #    Propositional encoding time       : 0.000
% 0.87/1.11  #    Propositional solver time         : 0.000
% 0.87/1.11  #    Success case prop preproc time    : 0.000
% 0.87/1.11  #    Success case prop encoding time   : 0.000
% 0.87/1.11  #    Success case prop solver time     : 0.000
% 0.87/1.11  # Current number of processed clauses  : 589
% 0.87/1.11  #    Positive orientable unit clauses  : 17
% 0.87/1.11  #    Positive unorientable unit clauses: 0
% 0.87/1.11  #    Negative unit clauses             : 1
% 0.87/1.11  #    Non-unit-clauses                  : 571
% 0.87/1.11  # Current number of unprocessed clauses: 55143
% 0.87/1.11  # ...number of literals in the above   : 139385
% 0.87/1.11  # Current number of archived formulas  : 0
% 0.87/1.11  # Current number of archived clauses   : 1134
% 0.87/1.11  # Clause-clause subsumption calls (NU) : 254529
% 0.87/1.11  # Rec. Clause-clause subsumption calls : 166123
% 0.87/1.11  # Non-unit clause-clause subsumptions  : 4554
% 0.87/1.11  # Unit Clause-clause subsumption calls : 4664
% 0.87/1.11  # Rewrite failures with RHS unbound    : 260
% 0.87/1.11  # BW rewrite match attempts            : 5614
% 0.87/1.11  # BW rewrite match successes           : 83
% 0.87/1.11  # Condensation attempts                : 0
% 0.87/1.11  # Condensation successes               : 0
% 0.87/1.11  # Termbank termtop insertions          : 1888409
% 0.87/1.11  
% 0.87/1.11  # -------------------------------------------------
% 0.87/1.11  # User time                : 0.726 s
% 0.87/1.11  # System time              : 0.037 s
% 0.87/1.11  # Total time               : 0.763 s
% 0.87/1.11  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
