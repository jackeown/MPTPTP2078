%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:45 EST 2020

% Result     : Theorem 1.41s
% Output     : CNFRefutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 188 expanded)
%              Number of clauses        :   32 (  69 expanded)
%              Number of leaves         :    9 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  221 ( 895 expanded)
%              Number of equality atoms :   40 ( 229 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & v2_funct_1(esk10_0)
    & r2_hidden(esk9_0,k2_relat_1(esk10_0))
    & ( esk9_0 != k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))
      | esk9_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk10_0),esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_11,plain,(
    ! [X41,X42,X43] :
      ( ( r2_hidden(X41,k1_relat_1(X43))
        | ~ r2_hidden(k4_tarski(X41,X42),X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( X42 = k1_funct_1(X43,X41)
        | ~ r2_hidden(k4_tarski(X41,X42),X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( ~ r2_hidden(X41,k1_relat_1(X43))
        | X42 != k1_funct_1(X43,X41)
        | r2_hidden(k4_tarski(X41,X42),X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_12,plain,(
    ! [X37] :
      ( ( v1_relat_1(k2_funct_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_1(k2_funct_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_13,negated_conjecture,
    ( esk9_0 != k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))
    | esk9_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk10_0),esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ r2_hidden(X38,k1_relat_1(X39))
      | k1_funct_1(k5_relat_1(X39,X40),X38) = k1_funct_1(X40,k1_funct_1(X39,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X36] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ v2_funct_1(X36)
      | k2_funct_1(X36) = k4_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk10_0),esk10_0),esk9_0) != esk9_0
    | k1_funct_1(X1,X2) != esk9_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_23,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(k4_tarski(X29,X30),X28)
        | r2_hidden(k4_tarski(X30,X29),X27)
        | X28 != k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X32,X31),X27)
        | r2_hidden(k4_tarski(X31,X32),X28)
        | X28 != k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)
        | ~ r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)
        | X28 = k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)
        | r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)
        | X28 = k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_26,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | v1_relat_1(k4_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_27,plain,(
    ! [X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X18),X16)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16) )
      & ( ~ r2_hidden(esk5_2(X22,X23),X23)
        | ~ r2_hidden(k4_tarski(X25,esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) )
      & ( r2_hidden(esk5_2(X22,X23),X23)
        | r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)
        | X23 = k2_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0)) != esk9_0
    | k1_funct_1(X1,X2) != esk9_0
    | ~ v1_funct_1(k2_funct_1(esk10_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))),X1)
    | ~ r2_hidden(esk9_0,k1_relat_1(k2_funct_1(esk10_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_17]),c_0_18]),c_0_22])])).

cnf(c_0_29,plain,
    ( v1_funct_1(k4_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_31,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X5)
        | r2_hidden(X9,X6)
        | X6 != k1_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)
        | X12 = k1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)
        | X12 = k1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk10_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk10_0),esk9_0),esk9_0),esk10_0)
    | ~ r2_hidden(esk9_0,k1_relat_1(k2_funct_1(esk10_0)))
    | ~ r2_hidden(k4_tarski(X2,esk9_0),X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_14]),c_0_17]),c_0_18])])]),c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17]),c_0_18])])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]),c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(esk10_0),esk9_0),esk9_0),esk10_0)
    | ~ r2_hidden(esk9_0,k1_relat_1(k4_relat_1(esk10_0)))
    | ~ r2_hidden(k4_tarski(X2,esk9_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_36]),c_0_30]),c_0_17]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_24]),c_0_30]),c_0_17]),c_0_18])])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k2_relat_1(X2),X1)),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk9_0,X2),k4_relat_1(esk10_0))
    | ~ r2_hidden(k4_tarski(X2,esk9_0),esk10_0)
    | ~ r2_hidden(k4_tarski(X3,esk9_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_14]),c_0_36]),c_0_41])]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk4_3(esk10_0,k2_relat_1(esk10_0),esk9_0)),k4_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_18])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk4_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0),esk10_0)
    | ~ r2_hidden(k4_tarski(X2,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,esk9_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_39]),c_0_44])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk9_0,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.41/1.65  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.41/1.65  # and selection function PSelectUnlessUniqMaxPos.
% 1.41/1.65  #
% 1.41/1.65  # Preprocessing time       : 0.044 s
% 1.41/1.65  # Presaturation interreduction done
% 1.41/1.65  
% 1.41/1.65  # Proof found!
% 1.41/1.65  # SZS status Theorem
% 1.41/1.65  # SZS output start CNFRefutation
% 1.41/1.65  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 1.41/1.65  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 1.41/1.65  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.41/1.65  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 1.41/1.65  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 1.41/1.65  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 1.41/1.65  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.41/1.65  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.41/1.65  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.41/1.65  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 1.41/1.65  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&((v2_funct_1(esk10_0)&r2_hidden(esk9_0,k2_relat_1(esk10_0)))&(esk9_0!=k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))|esk9_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk10_0),esk10_0),esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 1.41/1.65  fof(c_0_11, plain, ![X41, X42, X43]:(((r2_hidden(X41,k1_relat_1(X43))|~r2_hidden(k4_tarski(X41,X42),X43)|(~v1_relat_1(X43)|~v1_funct_1(X43)))&(X42=k1_funct_1(X43,X41)|~r2_hidden(k4_tarski(X41,X42),X43)|(~v1_relat_1(X43)|~v1_funct_1(X43))))&(~r2_hidden(X41,k1_relat_1(X43))|X42!=k1_funct_1(X43,X41)|r2_hidden(k4_tarski(X41,X42),X43)|(~v1_relat_1(X43)|~v1_funct_1(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 1.41/1.65  fof(c_0_12, plain, ![X37]:((v1_relat_1(k2_funct_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(v1_funct_1(k2_funct_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.41/1.65  cnf(c_0_13, negated_conjecture, (esk9_0!=k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))|esk9_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk10_0),esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.41/1.65  cnf(c_0_14, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.41/1.65  fof(c_0_15, plain, ![X38, X39, X40]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~v1_relat_1(X40)|~v1_funct_1(X40)|(~r2_hidden(X38,k1_relat_1(X39))|k1_funct_1(k5_relat_1(X39,X40),X38)=k1_funct_1(X40,k1_funct_1(X39,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 1.41/1.65  cnf(c_0_16, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.41/1.65  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.41/1.65  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.41/1.65  fof(c_0_19, plain, ![X36]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~v2_funct_1(X36)|k2_funct_1(X36)=k4_relat_1(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 1.41/1.65  cnf(c_0_20, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk10_0),esk10_0),esk9_0)!=esk9_0|k1_funct_1(X1,X2)!=esk9_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 1.41/1.65  cnf(c_0_21, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.41/1.65  cnf(c_0_22, negated_conjecture, (v1_relat_1(k2_funct_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 1.41/1.65  cnf(c_0_23, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.41/1.65  cnf(c_0_24, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.41/1.65  fof(c_0_25, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(k4_tarski(X29,X30),X28)|r2_hidden(k4_tarski(X30,X29),X27)|X28!=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27))&(~r2_hidden(k4_tarski(X32,X31),X27)|r2_hidden(k4_tarski(X31,X32),X28)|X28!=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27)))&((~r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)|~r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)|X28=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk7_2(X27,X28),esk8_2(X27,X28)),X28)|r2_hidden(k4_tarski(esk8_2(X27,X28),esk7_2(X27,X28)),X27)|X28=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 1.41/1.65  fof(c_0_26, plain, ![X35]:(~v1_relat_1(X35)|v1_relat_1(k4_relat_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 1.41/1.65  fof(c_0_27, plain, ![X16, X17, X18, X20, X21, X22, X23, X25]:(((~r2_hidden(X18,X17)|r2_hidden(k4_tarski(esk4_3(X16,X17,X18),X18),X16)|X17!=k2_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(X20,X17)|X17!=k2_relat_1(X16)))&((~r2_hidden(esk5_2(X22,X23),X23)|~r2_hidden(k4_tarski(X25,esk5_2(X22,X23)),X22)|X23=k2_relat_1(X22))&(r2_hidden(esk5_2(X22,X23),X23)|r2_hidden(k4_tarski(esk6_2(X22,X23),esk5_2(X22,X23)),X22)|X23=k2_relat_1(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.41/1.65  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))!=esk9_0|k1_funct_1(X1,X2)!=esk9_0|~v1_funct_1(k2_funct_1(esk10_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk10_0,k1_funct_1(k2_funct_1(esk10_0),esk9_0))),X1)|~r2_hidden(esk9_0,k1_relat_1(k2_funct_1(esk10_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_17]), c_0_18]), c_0_22])])).
% 1.41/1.65  cnf(c_0_29, plain, (v1_funct_1(k4_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.41/1.65  cnf(c_0_30, negated_conjecture, (v2_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.41/1.65  fof(c_0_31, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(X7,esk1_3(X5,X6,X7)),X5)|X6!=k1_relat_1(X5))&(~r2_hidden(k4_tarski(X9,X10),X5)|r2_hidden(X9,X6)|X6!=k1_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(esk2_2(X11,X12),X14),X11)|X12=k1_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)),X11)|X12=k1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.41/1.65  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k4_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.41/1.65  cnf(c_0_33, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.41/1.65  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.41/1.65  cnf(c_0_35, negated_conjecture, (~v1_funct_1(k2_funct_1(esk10_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk10_0),esk9_0),esk9_0),esk10_0)|~r2_hidden(esk9_0,k1_relat_1(k2_funct_1(esk10_0)))|~r2_hidden(k4_tarski(X2,esk9_0),X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_14]), c_0_17]), c_0_18])])]), c_0_14])).
% 1.41/1.65  cnf(c_0_36, negated_conjecture, (v1_funct_1(k4_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_17]), c_0_18])])).
% 1.41/1.65  cnf(c_0_37, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.41/1.65  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_32]), c_0_33])).
% 1.41/1.65  cnf(c_0_39, plain, (r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_34])).
% 1.41/1.65  cnf(c_0_40, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(esk10_0),esk9_0),esk9_0),esk10_0)|~r2_hidden(esk9_0,k1_relat_1(k4_relat_1(esk10_0)))|~r2_hidden(k4_tarski(X2,esk9_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_24]), c_0_36]), c_0_30]), c_0_17]), c_0_18])])).
% 1.41/1.65  cnf(c_0_41, negated_conjecture, (v1_relat_1(k4_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_24]), c_0_30]), c_0_17]), c_0_18])])).
% 1.41/1.65  cnf(c_0_42, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_37])).
% 1.41/1.65  cnf(c_0_43, plain, (r2_hidden(k4_tarski(X1,esk4_3(X2,k2_relat_1(X2),X1)),k4_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.41/1.65  cnf(c_0_44, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.41/1.65  cnf(c_0_45, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk9_0,X2),k4_relat_1(esk10_0))|~r2_hidden(k4_tarski(X2,esk9_0),esk10_0)|~r2_hidden(k4_tarski(X3,esk9_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_14]), c_0_36]), c_0_41])]), c_0_42])).
% 1.41/1.65  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk4_3(esk10_0,k2_relat_1(esk10_0),esk9_0)),k4_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_18])])).
% 1.41/1.65  cnf(c_0_47, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk4_3(esk10_0,k2_relat_1(esk10_0),esk9_0),esk9_0),esk10_0)|~r2_hidden(k4_tarski(X2,esk9_0),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.41/1.65  cnf(c_0_48, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,esk9_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_39]), c_0_44])])).
% 1.41/1.65  cnf(c_0_49, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk9_0,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_48, c_0_39])).
% 1.41/1.65  cnf(c_0_50, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_17]), c_0_18])]), ['proof']).
% 1.41/1.65  # SZS output end CNFRefutation
% 1.41/1.65  # Proof object total steps             : 51
% 1.41/1.65  # Proof object clause steps            : 32
% 1.41/1.65  # Proof object formula steps           : 19
% 1.41/1.65  # Proof object conjectures             : 21
% 1.41/1.65  # Proof object clause conjectures      : 18
% 1.41/1.65  # Proof object formula conjectures     : 3
% 1.41/1.65  # Proof object initial clauses used    : 14
% 1.41/1.65  # Proof object initial formulas used   : 9
% 1.41/1.65  # Proof object generating inferences   : 15
% 1.41/1.65  # Proof object simplifying inferences  : 38
% 1.41/1.65  # Training examples: 0 positive, 0 negative
% 1.41/1.65  # Parsed axioms                        : 9
% 1.41/1.65  # Removed by relevancy pruning/SinE    : 0
% 1.41/1.65  # Initial clauses                      : 25
% 1.41/1.65  # Removed in clause preprocessing      : 0
% 1.41/1.65  # Initial clauses in saturation        : 25
% 1.41/1.65  # Processed clauses                    : 1704
% 1.41/1.65  # ...of these trivial                  : 0
% 1.41/1.65  # ...subsumed                          : 505
% 1.41/1.65  # ...remaining for further processing  : 1199
% 1.41/1.65  # Other redundant clauses eliminated   : 2388
% 1.41/1.65  # Clauses deleted for lack of memory   : 0
% 1.41/1.65  # Backward-subsumed                    : 104
% 1.41/1.65  # Backward-rewritten                   : 7
% 1.41/1.65  # Generated clauses                    : 111124
% 1.41/1.65  # ...of the previous two non-trivial   : 108673
% 1.41/1.65  # Contextual simplify-reflections      : 53
% 1.41/1.65  # Paramodulations                      : 108734
% 1.41/1.65  # Factorizations                       : 2
% 1.41/1.65  # Equation resolutions                 : 2388
% 1.41/1.65  # Propositional unsat checks           : 0
% 1.41/1.65  #    Propositional check models        : 0
% 1.41/1.65  #    Propositional check unsatisfiable : 0
% 1.41/1.65  #    Propositional clauses             : 0
% 1.41/1.65  #    Propositional clauses after purity: 0
% 1.41/1.65  #    Propositional unsat core size     : 0
% 1.41/1.65  #    Propositional preprocessing time  : 0.000
% 1.41/1.65  #    Propositional encoding time       : 0.000
% 1.41/1.65  #    Propositional solver time         : 0.000
% 1.41/1.65  #    Success case prop preproc time    : 0.000
% 1.41/1.65  #    Success case prop encoding time   : 0.000
% 1.41/1.65  #    Success case prop solver time     : 0.000
% 1.41/1.65  # Current number of processed clauses  : 1057
% 1.41/1.65  #    Positive orientable unit clauses  : 41
% 1.41/1.65  #    Positive unorientable unit clauses: 0
% 1.41/1.65  #    Negative unit clauses             : 0
% 1.41/1.65  #    Non-unit-clauses                  : 1016
% 1.41/1.65  # Current number of unprocessed clauses: 106955
% 1.41/1.65  # ...number of literals in the above   : 848200
% 1.41/1.65  # Current number of archived formulas  : 0
% 1.41/1.65  # Current number of archived clauses   : 135
% 1.41/1.65  # Clause-clause subsumption calls (NU) : 357140
% 1.41/1.65  # Rec. Clause-clause subsumption calls : 51834
% 1.41/1.65  # Non-unit clause-clause subsumptions  : 662
% 1.41/1.65  # Unit Clause-clause subsumption calls : 5043
% 1.41/1.65  # Rewrite failures with RHS unbound    : 0
% 1.41/1.65  # BW rewrite match attempts            : 4063
% 1.41/1.65  # BW rewrite match successes           : 1
% 1.41/1.65  # Condensation attempts                : 0
% 1.41/1.65  # Condensation successes               : 0
% 1.41/1.65  # Termbank termtop insertions          : 3509664
% 1.49/1.66  
% 1.49/1.66  # -------------------------------------------------
% 1.49/1.66  # User time                : 1.237 s
% 1.49/1.66  # System time              : 0.076 s
% 1.49/1.66  # Total time               : 1.313 s
% 1.49/1.66  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
