%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t85_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 266.70s
% Output     : CNFRefutation 266.70s
% Verified   : 
% Statistics : Number of formulae       :  163 (994127 expanded)
%              Number of clauses        :  150 (398508 expanded)
%              Number of leaves         :    6 (225639 expanded)
%              Depth                    :   41
%              Number of atoms          :  603 (12549983 expanded)
%              Number of equality atoms :  222 (3458201 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   43 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',d4_funct_1)).

fof(t85_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( X2 = k8_relat_1(X1,X3)
          <=> ( ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(X4,k1_relat_1(X3))
                    & r2_hidden(k1_funct_1(X3,X4),X1) ) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',t85_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',d12_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',t8_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',d4_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t85_funct_1.p',dt_k8_relat_1)).

fof(c_0_6,plain,(
    ! [X24,X25,X26] :
      ( ( X26 != k1_funct_1(X24,X25)
        | r2_hidden(k4_tarski(X25,X26),X24)
        | ~ r2_hidden(X25,k1_relat_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X25,X26),X24)
        | X26 = k1_funct_1(X24,X25)
        | ~ r2_hidden(X25,k1_relat_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( X26 != k1_funct_1(X24,X25)
        | X26 = k1_xboole_0
        | r2_hidden(X25,k1_relat_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( X26 != k1_xboole_0
        | X26 = k1_funct_1(X24,X25)
        | r2_hidden(X25,k1_relat_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( X2 = k8_relat_1(X1,X3)
            <=> ( ! [X4] :
                    ( r2_hidden(X4,k1_relat_1(X2))
                  <=> ( r2_hidden(X4,k1_relat_1(X3))
                      & r2_hidden(k1_funct_1(X3,X4),X1) ) )
                & ! [X4] :
                    ( r2_hidden(X4,k1_relat_1(X2))
                   => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_funct_1])).

cnf(c_0_8,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,(
    ! [X11,X12] :
      ( v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
        | ~ r2_hidden(esk4_0,k1_relat_1(esk2_0))
        | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0))
        | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
        | esk2_0 != k8_relat_1(esk1_0,esk3_0) )
      & ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
        | ~ r2_hidden(esk4_0,k1_relat_1(esk2_0))
        | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0))
        | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
        | esk2_0 != k8_relat_1(esk1_0,esk3_0) )
      & ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
        | r2_hidden(esk4_0,k1_relat_1(esk3_0))
        | r2_hidden(esk4_0,k1_relat_1(esk2_0))
        | esk2_0 != k8_relat_1(esk1_0,esk3_0) )
      & ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
        | r2_hidden(esk4_0,k1_relat_1(esk3_0))
        | r2_hidden(esk4_0,k1_relat_1(esk2_0))
        | esk2_0 != k8_relat_1(esk1_0,esk3_0) )
      & ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
        | r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
        | r2_hidden(esk4_0,k1_relat_1(esk2_0))
        | esk2_0 != k8_relat_1(esk1_0,esk3_0) )
      & ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
        | r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
        | r2_hidden(esk4_0,k1_relat_1(esk2_0))
        | esk2_0 != k8_relat_1(esk1_0,esk3_0) )
      & ( r2_hidden(X11,k1_relat_1(esk3_0))
        | ~ r2_hidden(X11,k1_relat_1(esk2_0))
        | esk2_0 = k8_relat_1(esk1_0,esk3_0) )
      & ( r2_hidden(k1_funct_1(esk3_0,X11),esk1_0)
        | ~ r2_hidden(X11,k1_relat_1(esk2_0))
        | esk2_0 = k8_relat_1(esk1_0,esk3_0) )
      & ( ~ r2_hidden(X11,k1_relat_1(esk3_0))
        | ~ r2_hidden(k1_funct_1(esk3_0,X11),esk1_0)
        | r2_hidden(X11,k1_relat_1(esk2_0))
        | esk2_0 = k8_relat_1(esk1_0,esk3_0) )
      & ( ~ r2_hidden(X12,k1_relat_1(esk2_0))
        | k1_funct_1(esk2_0,X12) = k1_funct_1(esk3_0,X12)
        | esk2_0 = k8_relat_1(esk1_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X19,X15)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k8_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(X18,X19),X16)
        | ~ r2_hidden(k4_tarski(X18,X19),X17)
        | X17 != k8_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(X21,X15)
        | ~ r2_hidden(k4_tarski(X20,X21),X16)
        | r2_hidden(k4_tarski(X20,X21),X17)
        | X17 != k8_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X17)
        | ~ r2_hidden(esk7_3(X15,X16,X17),X15)
        | ~ r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X16)
        | X17 = k8_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk7_3(X15,X16,X17),X15)
        | r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X17)
        | X17 = k8_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X16)
        | r2_hidden(k4_tarski(esk6_3(X15,X16,X17),esk7_3(X15,X16,X17)),X17)
        | X17 = k8_relat_1(X15,X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

cnf(c_0_11,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | esk2_0 = k8_relat_1(esk1_0,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

fof(c_0_17,plain,(
    ! [X51,X52,X53] :
      ( ( r2_hidden(X51,k1_relat_1(X53))
        | ~ r2_hidden(k4_tarski(X51,X52),X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( X52 = k1_funct_1(X53,X51)
        | ~ r2_hidden(k4_tarski(X51,X52),X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( ~ r2_hidden(X51,k1_relat_1(X53))
        | X52 != k1_funct_1(X53,X51)
        | r2_hidden(k4_tarski(X51,X52),X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_18,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk2_0)
    | r2_hidden(k4_tarski(esk6_3(X2,esk2_0,X1),esk7_3(X2,esk2_0,X1)),esk2_0)
    | r2_hidden(k4_tarski(esk6_3(X2,esk2_0,X1),esk7_3(X2,esk2_0,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

fof(c_0_19,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(X29,esk8_3(X27,X28,X29)),X27)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X31,X32),X27)
        | r2_hidden(X31,X28)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(esk9_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(esk9_2(X33,X34),X36),X33)
        | X34 = k1_relat_1(X33) )
      & ( r2_hidden(esk9_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk9_2(X33,X34),esk10_2(X33,X34)),X33)
        | X34 = k1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,X1),esk1_0)
    | esk2_0 = k8_relat_1(esk1_0,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk2_0,X1)
    | k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k1_funct_1(esk2_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( k8_relat_1(X1,esk2_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(X1,esk2_0,esk2_0),esk7_3(X1,esk2_0,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk2_0,X1),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(esk2_0,esk6_3(X1,esk2_0,esk2_0)) = esk7_3(X1,esk2_0,esk2_0)
    | k8_relat_1(X1,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_12]),c_0_13])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( X3 = k8_relat_1(X1,X2)
    | ~ r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X1)
    | ~ r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( esk7_3(X1,esk2_0,esk2_0) = k1_xboole_0
    | k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(X1,esk2_0) = esk2_0
    | r2_hidden(esk7_3(X1,esk2_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k8_relat_1(X1,esk2_0) = esk2_0
    | r2_hidden(esk6_3(X1,esk2_0,esk2_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( esk7_3(esk1_0,esk2_0,esk2_0) = k1_xboole_0
    | k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(esk1_0,esk2_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_13])]),c_0_23])).

fof(c_0_32,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | v1_relat_1(k8_relat_1(X38,X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(X1,esk2_0,esk2_0)) = k1_funct_1(esk2_0,esk6_3(X1,esk2_0,esk2_0))
    | k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(X1,esk2_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(esk1_0,esk2_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(esk1_0,esk2_0,esk2_0),k1_xboole_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(esk1_0,esk2_0) = esk2_0
    | ~ r2_hidden(k4_tarski(esk6_3(esk1_0,esk2_0,esk2_0),k1_xboole_0),esk2_0)
    | ~ r2_hidden(k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_13])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(X1,esk2_0) = esk2_0
    | r2_hidden(k1_funct_1(esk2_0,esk6_3(X1,esk2_0,esk2_0)),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_33]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk2_0,esk6_3(esk1_0,esk2_0,esk2_0)) = k1_xboole_0
    | k8_relat_1(esk1_0,esk2_0) = esk2_0
    | k8_relat_1(esk1_0,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_34]),c_0_12]),c_0_13])])).

cnf(c_0_40,negated_conjecture,
    ( k8_relat_1(esk1_0,esk2_0) = esk2_0
    | k8_relat_1(esk1_0,esk3_0) = esk2_0
    | ~ r2_hidden(k1_xboole_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k8_relat_1(X2,X4))
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k8_relat_1(esk1_0,esk2_0) = esk2_0
    | k8_relat_1(esk1_0,esk3_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( k8_relat_1(esk1_0,esk2_0) = esk2_0
    | r2_hidden(X1,esk1_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

cnf(c_0_45,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk3_0)
    | r2_hidden(k4_tarski(esk6_3(X2,esk3_0,X1),esk7_3(X2,esk3_0,X1)),esk3_0)
    | r2_hidden(k4_tarski(esk6_3(X2,esk3_0,X1),esk7_3(X2,esk3_0,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( k8_relat_1(esk1_0,esk2_0) = esk2_0
    | k8_relat_1(X1,esk2_0) = esk2_0
    | r2_hidden(esk7_3(X1,esk2_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_47,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X1)
    | r2_hidden(k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(X1,esk3_0,esk2_0),esk7_3(X1,esk3_0,esk2_0)),esk2_0)
    | r2_hidden(k4_tarski(esk6_3(X1,esk3_0,esk2_0),esk7_3(X1,esk3_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,negated_conjecture,
    ( k8_relat_1(esk1_0,esk2_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_46]),c_0_13])]),c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( X1 = k8_relat_1(X2,esk3_0)
    | r2_hidden(k4_tarski(esk6_3(X2,esk3_0,X1),esk7_3(X2,esk3_0,X1)),X1)
    | r2_hidden(esk7_3(X2,esk3_0,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(X1,esk3_0,esk2_0)) = esk7_3(X1,esk3_0,esk2_0)
    | k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(X1,esk3_0,esk2_0),esk7_3(X1,esk3_0,esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_48]),c_0_49]),c_0_43])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk1_0)
    | ~ r2_hidden(k4_tarski(X2,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_50]),c_0_13])])).

cnf(c_0_54,negated_conjecture,
    ( k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(X1,esk3_0,esk2_0),esk7_3(X1,esk3_0,esk2_0)),esk2_0)
    | r2_hidden(esk7_3(X1,esk3_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_13])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(X1,esk3_0,esk2_0)) = esk7_3(X1,esk3_0,esk2_0)
    | k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(esk6_3(X1,esk3_0,esk2_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(esk7_3(X1,esk3_0,esk2_0),esk1_0)
    | r2_hidden(esk7_3(X1,esk3_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk3_0))
    | esk2_0 = k8_relat_1(esk1_0,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(X1,esk3_0,esk2_0)) = k1_funct_1(esk2_0,esk6_3(X1,esk3_0,esk2_0))
    | k1_funct_1(esk3_0,esk6_3(X1,esk3_0,esk2_0)) = esk7_3(X1,esk3_0,esk2_0)
    | k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(X1,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(X1,esk3_0,esk2_0)) = esk7_3(X1,esk3_0,esk2_0)
    | k1_funct_1(esk2_0,esk6_3(X1,esk3_0,esk2_0)) = esk7_3(X1,esk3_0,esk2_0)
    | k8_relat_1(X1,esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_52]),c_0_12]),c_0_13])])).

cnf(c_0_62,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | r2_hidden(esk7_3(esk1_0,esk3_0,esk2_0),esk1_0) ),
    inference(ef,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk3_0,X1)),esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_49]),c_0_43])])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(X1,esk3_0,esk2_0)) = esk7_3(X1,esk3_0,esk2_0)
    | k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(X1,esk3_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_60]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(X1,esk3_0,esk2_0),esk7_3(X1,esk3_0,esk2_0)),esk2_0)
    | r2_hidden(esk6_3(X1,esk3_0,esk2_0),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_48])).

cnf(c_0_66,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | ~ r2_hidden(k4_tarski(esk6_3(esk1_0,esk3_0,esk2_0),esk7_3(esk1_0,esk3_0,esk2_0)),esk2_0)
    | ~ r2_hidden(k4_tarski(esk6_3(esk1_0,esk3_0,esk2_0),esk7_3(esk1_0,esk3_0,esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_62]),c_0_13]),c_0_43])])).

cnf(c_0_67,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(X1,esk3_0,esk2_0),esk7_3(X1,esk3_0,esk2_0)),esk3_0)
    | ~ r2_hidden(esk6_3(X1,esk3_0,esk2_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk2_0))
    | esk2_0 = k8_relat_1(esk1_0,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,X1),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_69,negated_conjecture,
    ( k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(esk6_3(X1,esk3_0,esk2_0),k1_relat_1(esk3_0))
    | r2_hidden(esk6_3(X1,esk3_0,esk2_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | ~ r2_hidden(k4_tarski(esk6_3(esk1_0,esk3_0,esk2_0),esk7_3(esk1_0,esk3_0,esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_27])).

cnf(c_0_71,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | k8_relat_1(X1,esk3_0) = esk2_0
    | r2_hidden(esk6_3(X1,esk3_0,esk2_0),k1_relat_1(esk2_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk6_3(X1,esk3_0,esk2_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(esk1_0,esk3_0,esk2_0)) = esk7_3(esk1_0,esk3_0,esk2_0)
    | k8_relat_1(esk1_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_52])).

cnf(c_0_73,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | r2_hidden(esk6_3(esk1_0,esk3_0,esk2_0),k1_relat_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_62])).

cnf(c_0_74,plain,
    ( r2_hidden(k4_tarski(X3,X1),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X5 != k8_relat_1(X2,X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk3_0))
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
    | esk2_0 != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_76,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | X4 != k8_relat_1(X5,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk3_0,esk6_3(esk1_0,esk3_0,esk2_0)) = k1_funct_1(esk2_0,esk6_3(esk1_0,esk3_0,esk2_0))
    | k8_relat_1(esk1_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_73])).

cnf(c_0_78,plain,
    ( r2_hidden(k4_tarski(X1,X2),k8_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X1,X2),X4)
    | ~ r2_hidden(X2,X3)
    | ~ v1_relat_1(X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_37])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk3_0,esk4_0)),esk3_0)
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0)
    | k8_relat_1(esk1_0,esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_75]),c_0_49]),c_0_43])])).

cnf(c_0_80,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(X4,X3))
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_76]),c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0
    | r2_hidden(k4_tarski(esk6_3(esk1_0,esk3_0,esk2_0),k1_funct_1(esk2_0,esk6_3(esk1_0,esk3_0,esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_73]),c_0_12]),c_0_13])])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(esk2_0,esk6_3(esk1_0,esk3_0,esk2_0)) = esk7_3(esk1_0,esk3_0,esk2_0)
    | k8_relat_1(esk1_0,esk3_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_77])).

cnf(c_0_83,plain,
    ( r2_hidden(k4_tarski(X1,esk8_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk3_0,esk4_0)),k8_relat_1(X1,esk3_0))
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0)
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_43])])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk2_0,X1)
    | k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,X3),esk3_0)
    | ~ r2_hidden(k4_tarski(X2,X3),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_21]),c_0_43])])).

cnf(c_0_86,negated_conjecture,
    ( k8_relat_1(esk1_0,esk3_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_70])).

cnf(c_0_87,plain,
    ( r2_hidden(k4_tarski(X1,esk8_3(k8_relat_1(X2,X3),X4,X1)),X3)
    | X4 != k1_relat_1(k8_relat_1(X2,X3))
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_80,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k8_relat_1(X1,esk3_0)))
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0)
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
    | esk2_0 != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk2_0,X1)
    | k1_funct_1(esk2_0,X1) = k1_xboole_0
    | X2 = k1_funct_1(esk3_0,X3)
    | ~ r2_hidden(k4_tarski(X3,X2),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_85]),c_0_49]),c_0_43])])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk2_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_12]),c_0_13])])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk3_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_86]),c_0_43])])).

cnf(c_0_93,plain,
    ( r2_hidden(k4_tarski(X1,esk8_3(k8_relat_1(X2,X3),k1_relat_1(k8_relat_1(X2,X3)),X1)),X3)
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X2,X3)))
    | ~ v1_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k8_relat_1(X1,esk3_0)))
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_86])])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_86])])).

cnf(c_0_96,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk2_0,X1)
    | k1_funct_1(esk3_0,X2) = k1_funct_1(esk2_0,X2)
    | k1_funct_1(esk2_0,X1) = k1_xboole_0
    | k1_funct_1(esk2_0,X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | r2_hidden(esk4_0,k1_relat_1(esk3_0))
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | esk2_0 != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_92])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_3(esk2_0,k1_relat_1(esk2_0),X1)),esk2_0)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_50]),c_0_13])])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_86]),c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_49]),c_0_43])])).

cnf(c_0_102,plain,
    ( esk8_3(X1,X2,X3) = k1_funct_1(X1,X3)
    | X2 != k1_relat_1(X1)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_83])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | esk2_0 != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk2_0,X1)
    | k1_funct_1(esk2_0,X1) = k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk2_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_91])).

cnf(c_0_106,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk2_0,esk5_0)),esk2_0)
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | r2_hidden(esk4_0,k1_relat_1(esk3_0))
    | k8_relat_1(esk1_0,esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_97]),c_0_12]),c_0_13])])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk3_0))
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_108,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk2_0,esk4_0)),esk2_0)
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_100]),c_0_12]),c_0_13])])).

cnf(c_0_109,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk3_0,X1)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_101]),c_0_49]),c_0_43])])).

cnf(c_0_110,plain,
    ( esk8_3(X1,k1_relat_1(X1),X2) = k1_funct_1(X1,X2)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_111,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_16]),c_0_105])).

cnf(c_0_112,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_113,negated_conjecture,
    ( X1 = k1_funct_1(esk3_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_92]),c_0_49]),c_0_43])])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk2_0,esk5_0)),esk2_0)
    | r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_86])]),c_0_107])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk3_0))
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_108])).

cnf(c_0_116,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_3(esk2_0,k1_relat_1(esk2_0),X1)),k8_relat_1(X2,esk2_0))
    | ~ r2_hidden(esk8_3(esk2_0,k1_relat_1(esk2_0),X1),X2)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_99]),c_0_13])])).

cnf(c_0_117,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk2_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_104])).

cnf(c_0_118,negated_conjecture,
    ( esk8_3(esk2_0,k1_relat_1(esk2_0),esk5_0) = k1_funct_1(esk2_0,esk5_0)
    | k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_12]),c_0_13])])).

cnf(c_0_119,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | X2 = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk3_0))
    | X2 != k1_funct_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_104]),c_0_49]),c_0_43])])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk2_0)))
    | ~ r2_hidden(esk8_3(esk2_0,k1_relat_1(esk2_0),X1),X2)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( esk8_3(esk2_0,k1_relat_1(esk2_0),esk5_0) = k1_funct_1(esk2_0,esk5_0)
    | k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | X1 = k1_xboole_0
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | X1 != k1_funct_1(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk3_0,esk4_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_120]),c_0_49]),c_0_43])])).

cnf(c_0_125,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) != k1_funct_1(esk3_0,esk5_0)
    | ~ r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | esk2_0 != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_126,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(k8_relat_1(X1,esk2_0)))
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(esk8_3(esk2_0,k1_relat_1(esk2_0),esk5_0),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_111]),c_0_122])).

cnf(c_0_127,negated_conjecture,
    ( esk8_3(esk2_0,k1_relat_1(esk2_0),esk5_0) = k1_funct_1(esk2_0,esk5_0)
    | k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | k8_relat_1(esk1_0,esk3_0) != esk2_0 ),
    inference(er,[status(thm)],[c_0_123])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(esk3_0,esk4_0)),k8_relat_1(X1,esk3_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_124]),c_0_43])])).

cnf(c_0_129,plain,
    ( r2_hidden(esk8_3(k8_relat_1(X1,X2),X3,X4),X1)
    | X3 != k1_relat_1(k8_relat_1(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_83])).

cnf(c_0_130,negated_conjecture,
    ( esk8_3(esk2_0,k1_relat_1(esk2_0),X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_99])).

cnf(c_0_131,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | ~ r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_86])])).

cnf(c_0_132,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(k8_relat_1(X1,esk2_0)))
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(k1_funct_1(esk2_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk2_0,esk5_0)),esk2_0)
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_111]),c_0_12]),c_0_13])])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k8_relat_1(X1,esk3_0)))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_128])).

cnf(c_0_135,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | esk2_0 != k8_relat_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk8_3(esk2_0,X1,X2),esk1_0)
    | X1 != k1_relat_1(esk2_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_50]),c_0_13])])).

cnf(c_0_137,negated_conjecture,
    ( esk8_3(esk2_0,k1_relat_1(esk2_0),esk4_0) = k1_funct_1(esk3_0,esk4_0)
    | k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_100])).

cnf(c_0_138,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0)
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_120])]),c_0_100])).

cnf(c_0_139,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(k1_funct_1(esk2_0,esk5_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_50])).

cnf(c_0_140,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk2_0,esk5_0),esk1_0)
    | k8_relat_1(esk1_0,esk3_0) != esk2_0
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_133])).

cnf(c_0_141,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_134,c_0_86])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | r2_hidden(esk5_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_86])])).

cnf(c_0_143,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) != k1_funct_1(esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_100]),c_0_138])).

cnf(c_0_144,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(k1_funct_1(esk2_0,esk5_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_86])])).

cnf(c_0_145,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk2_0,esk5_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_86])]),c_0_122])).

cnf(c_0_146,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | r2_hidden(esk4_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_147,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_143,c_0_104])).

cnf(c_0_148,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_149,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_xboole_0),esk2_0)
    | r2_hidden(esk4_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_146]),c_0_147]),c_0_12]),c_0_13])])).

cnf(c_0_150,negated_conjecture,
    ( k1_funct_1(esk3_0,esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_143,c_0_147])).

cnf(c_0_151,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_0,k1_xboole_0),esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_148]),c_0_12]),c_0_13])]),c_0_147])).

cnf(c_0_152,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | ~ r2_hidden(esk4_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(esk4_0,k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_86])])).

cnf(c_0_153,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_149]),c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_151]),c_0_150])).

cnf(c_0_155,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0)
    | ~ r2_hidden(esk4_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_152,c_0_120])])).

cnf(c_0_156,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_xboole_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_153]),c_0_154]),c_0_12]),c_0_13])])).

cnf(c_0_157,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0))
    | ~ r2_hidden(k1_funct_1(esk3_0,esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_155,c_0_153])])).

cnf(c_0_158,negated_conjecture,
    ( k1_funct_1(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_113,c_0_156])).

cnf(c_0_159,negated_conjecture,
    ( r2_hidden(k1_xboole_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_156])).

cnf(c_0_160,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_157,c_0_158]),c_0_159])])).

cnf(c_0_161,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_xboole_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_160]),c_0_147]),c_0_12]),c_0_13])])).

cnf(c_0_162,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_161]),c_0_150]),
    [proof]).
%------------------------------------------------------------------------------
