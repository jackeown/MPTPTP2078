%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t34_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 729 expanded)
%              Number of clauses        :   34 ( 287 expanded)
%              Number of leaves         :    6 ( 169 expanded)
%              Depth                    :   12
%              Number of atoms          :  202 (4966 expanded)
%              Number of equality atoms :   82 (2337 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t34_funct_1.p',t8_funct_1)).

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t34_funct_1.p',d10_relat_1)).

fof(t34_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t34_funct_1.p',t34_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t34_funct_1.p',d4_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t34_funct_1.p',t71_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t34_funct_1.p',dt_k6_relat_1)).

fof(c_0_6,plain,(
    ! [X35,X36,X37] :
      ( ( r2_hidden(X35,k1_relat_1(X37))
        | ~ r2_hidden(k4_tarski(X35,X36),X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( X36 = k1_funct_1(X37,X35)
        | ~ r2_hidden(k4_tarski(X35,X36),X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( ~ r2_hidden(X35,k1_relat_1(X37))
        | X36 != k1_funct_1(X37,X35)
        | r2_hidden(k4_tarski(X35,X36),X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X13,X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( X13 = X14
        | ~ r2_hidden(k4_tarski(X13,X14),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(X15,X11)
        | X15 != X16
        | r2_hidden(k4_tarski(X15,X16),X12)
        | X12 != k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X11,X12),esk5_2(X11,X12)),X12)
        | ~ r2_hidden(esk4_2(X11,X12),X11)
        | esk4_2(X11,X12) != esk5_2(X11,X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk4_2(X11,X12),X11)
        | r2_hidden(k4_tarski(esk4_2(X11,X12),esk5_2(X11,X12)),X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) )
      & ( esk4_2(X11,X12) = esk5_2(X11,X12)
        | r2_hidden(k4_tarski(esk4_2(X11,X12),esk5_2(X11,X12)),X12)
        | X12 = k6_relat_1(X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( X2 = k6_relat_1(X1)
        <=> ( k1_relat_1(X2) = X1
            & ! [X3] :
                ( r2_hidden(X3,X1)
               => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_funct_1])).

fof(c_0_11,plain,(
    ! [X19,X20,X21] :
      ( ( X21 != k1_funct_1(X19,X20)
        | r2_hidden(k4_tarski(X20,X21),X19)
        | ~ r2_hidden(X20,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X19)
        | X21 = k1_funct_1(X19,X20)
        | ~ r2_hidden(X20,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X21 != k1_funct_1(X19,X20)
        | X21 = k1_xboole_0
        | r2_hidden(X20,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( X21 != k1_xboole_0
        | X21 = k1_funct_1(X19,X20)
        | r2_hidden(X20,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_12,plain,
    ( X1 = k6_relat_1(X2)
    | r2_hidden(esk4_2(X2,X1),k1_relat_1(X1))
    | r2_hidden(esk4_2(X2,X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

fof(c_0_13,negated_conjecture,(
    ! [X8] :
      ( v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & ( r2_hidden(esk3_0,esk1_0)
        | k1_relat_1(esk2_0) != esk1_0
        | esk2_0 != k6_relat_1(esk1_0) )
      & ( k1_funct_1(esk2_0,esk3_0) != esk3_0
        | k1_relat_1(esk2_0) != esk1_0
        | esk2_0 != k6_relat_1(esk1_0) )
      & ( k1_relat_1(esk2_0) = esk1_0
        | esk2_0 = k6_relat_1(esk1_0) )
      & ( ~ r2_hidden(X8,esk1_0)
        | k1_funct_1(esk2_0,X8) = X8
        | esk2_0 = k6_relat_1(esk1_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( esk4_2(X1,X2) = esk5_2(X1,X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk4_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(ef,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0
    | esk2_0 = k6_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( esk5_2(X1,X2) = k1_funct_1(X2,esk4_2(X1,X2))
    | esk5_2(X1,X2) = esk4_2(X1,X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = X1
    | esk2_0 = k6_relat_1(esk1_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk2_0
    | r2_hidden(esk4_2(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk2_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk2_0,X1)),esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_26,plain,
    ( esk5_2(X1,X2) = esk4_2(X1,X2)
    | X2 = k6_relat_1(X1)
    | k1_funct_1(X2,esk4_2(X1,X2)) != esk4_2(X1,X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(ef,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_2(esk1_0,esk2_0)) = esk4_2(esk1_0,esk2_0)
    | k6_relat_1(esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk2_0
    | r2_hidden(k4_tarski(esk4_2(esk1_0,esk2_0),k1_funct_1(esk2_0,esk4_2(esk1_0,esk2_0))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

fof(c_0_29,plain,(
    ! [X30] :
      ( k1_relat_1(k6_relat_1(X30)) = X30
      & k2_relat_1(k6_relat_1(X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_30,plain,
    ( X2 = k6_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | ~ r2_hidden(esk4_2(X1,X2),X1)
    | esk4_2(X1,X2) != esk5_2(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( esk5_2(esk1_0,esk2_0) = esk4_2(esk1_0,esk2_0)
    | k6_relat_1(esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19]),c_0_20])])).

cnf(c_0_32,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk2_0
    | r2_hidden(k4_tarski(esk4_2(esk1_0,esk2_0),esk4_2(esk1_0,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_34,plain,(
    ! [X22] : v1_relat_1(k6_relat_1(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_35,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_20])]),c_0_24]),c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | X2 != k6_relat_1(X3)
    | ~ r2_hidden(X1,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0)
    | k1_relat_1(esk2_0) != esk1_0
    | esk2_0 != k6_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_36])]),c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_0) != esk3_0
    | k1_relat_1(esk2_0) != esk1_0
    | esk2_0 != k6_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk3_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk2_0,esk3_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_36])]),c_0_40])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_44]),c_0_19]),c_0_20])]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
