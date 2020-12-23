%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:06 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 416 expanded)
%              Number of clauses        :   43 ( 157 expanded)
%              Number of leaves         :    6 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  214 (3026 expanded)
%              Number of equality atoms :   59 (1200 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t156_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_relat_1(X4)
                & v1_funct_1(X4) )
             => ( ( X1 = k2_relat_1(X2)
                  & k1_relat_1(X3) = X1
                  & k1_relat_1(X4) = X1
                  & k5_relat_1(X2,X3) = k5_relat_1(X2,X4) )
               => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_1)).

fof(d2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X1 = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X1)
              <=> r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

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

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( v1_relat_1(X4)
                  & v1_funct_1(X4) )
               => ( ( X1 = k2_relat_1(X2)
                    & k1_relat_1(X3) = X1
                    & k1_relat_1(X4) = X1
                    & k5_relat_1(X2,X3) = k5_relat_1(X2,X4) )
                 => X3 = X4 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t156_funct_1])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(k4_tarski(X7,X8),X5)
        | r2_hidden(k4_tarski(X7,X8),X6)
        | X5 != X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X9,X10),X6)
        | r2_hidden(k4_tarski(X9,X10),X5)
        | X5 != X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)
        | ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X5 = X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X5 = X6
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & v1_relat_1(esk11_0)
    & v1_funct_1(esk11_0)
    & v1_relat_1(esk12_0)
    & v1_funct_1(esk12_0)
    & esk9_0 = k2_relat_1(esk10_0)
    & k1_relat_1(esk11_0) = esk9_0
    & k1_relat_1(esk12_0) = esk9_0
    & k5_relat_1(esk10_0,esk11_0) = k5_relat_1(esk10_0,esk12_0)
    & esk11_0 != esk12_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X38,X39,X40] :
      ( ( r2_hidden(X38,k1_relat_1(X40))
        | ~ r2_hidden(k4_tarski(X38,X39),X40)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( X39 = k1_funct_1(X40,X38)
        | ~ r2_hidden(k4_tarski(X38,X39),X40)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( ~ r2_hidden(X38,k1_relat_1(X40))
        | X39 != k1_funct_1(X40,X38)
        | r2_hidden(k4_tarski(X38,X39),X40)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X1 = X2
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( k1_relat_1(esk12_0) = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( esk9_0 = k2_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ r2_hidden(X35,k1_relat_1(X36))
      | k1_funct_1(k5_relat_1(X36,X37),X35) = k1_funct_1(X37,k1_funct_1(X36,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_16,negated_conjecture,
    ( X1 = esk11_0
    | r2_hidden(k4_tarski(esk1_2(X1,esk11_0),esk2_2(X1,esk11_0)),esk11_0)
    | r2_hidden(k4_tarski(esk1_2(X1,esk11_0),esk2_2(X1,esk11_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( esk11_0 != esk12_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(esk12_0) = k2_relat_1(esk10_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k5_relat_1(esk10_0,esk11_0) = k5_relat_1(esk10_0,esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_26,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X26),X24)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(esk7_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk7_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) )
      & ( r2_hidden(esk7_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_27,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk3_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk4_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk4_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk4_2(X19,X20),esk5_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_28,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk12_0)
    | r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk11_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk12_0,X1)),esk12_0)
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_17])])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk12_0,k1_funct_1(esk10_0,X1)) = k1_funct_1(k5_relat_1(esk10_0,esk11_0),X1)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_21]),c_0_24]),c_0_17]),c_0_25])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk2_2(esk12_0,esk11_0) = k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0))
    | r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_21]),c_0_17])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk10_0,X1),k1_funct_1(k5_relat_1(esk10_0,esk11_0),X1)),esk12_0)
    | ~ r2_hidden(k1_funct_1(esk10_0,X1),k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( esk2_2(esk12_0,esk11_0) = k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0))
    | esk2_2(esk12_0,esk11_0) = k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_34]),c_0_35]),c_0_11])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk10_0,X1),k1_funct_1(esk11_0,k1_funct_1(esk10_0,X1))),esk12_0)
    | ~ r2_hidden(k1_funct_1(esk10_0,X1),k2_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_22]),c_0_35]),c_0_24]),c_0_11]),c_0_25])])).

cnf(c_0_41,plain,
    ( k1_funct_1(X1,esk6_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk11_0) = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( esk2_2(esk12_0,esk11_0) = k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))
    | k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0)) != k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0)) ),
    inference(ef,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk11_0,X1)),esk12_0)
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_24]),c_0_25])]),c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk11_0)
    | r2_hidden(esk1_2(esk12_0,esk11_0),k2_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk11_0) = k2_relat_1(esk10_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0)) != k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))
    | ~ r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk11_0)
    | ~ r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk12_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_11]),c_0_17])]),c_0_18])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk12_0,X1) = k1_funct_1(esk11_0,X1)
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_46]),c_0_21]),c_0_17])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(esk12_0,esk11_0),k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_47]),c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk11_0)
    | ~ r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk12_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_51])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk11_0,X1)),esk11_0)
    | ~ r2_hidden(X1,k2_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_48]),c_0_35]),c_0_11])])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.52  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.52  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.52  #
% 0.19/0.52  # Preprocessing time       : 0.028 s
% 0.19/0.52  # Presaturation interreduction done
% 0.19/0.52  
% 0.19/0.52  # Proof found!
% 0.19/0.52  # SZS status Theorem
% 0.19/0.52  # SZS output start CNFRefutation
% 0.19/0.52  fof(t156_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_funct_1)).
% 0.19/0.52  fof(d2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X1=X2<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)<=>r2_hidden(k4_tarski(X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_relat_1)).
% 0.19/0.52  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.52  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 0.19/0.52  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.52  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.19/0.52  fof(c_0_6, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4))))), inference(assume_negation,[status(cth)],[t156_funct_1])).
% 0.19/0.52  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(k4_tarski(X7,X8),X5)|r2_hidden(k4_tarski(X7,X8),X6)|X5!=X6|~v1_relat_1(X6)|~v1_relat_1(X5))&(~r2_hidden(k4_tarski(X9,X10),X6)|r2_hidden(k4_tarski(X9,X10),X5)|X5!=X6|~v1_relat_1(X6)|~v1_relat_1(X5)))&((~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)|~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X5=X6|~v1_relat_1(X6)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X5=X6|~v1_relat_1(X6)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).
% 0.19/0.52  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&((v1_relat_1(esk11_0)&v1_funct_1(esk11_0))&((v1_relat_1(esk12_0)&v1_funct_1(esk12_0))&((((esk9_0=k2_relat_1(esk10_0)&k1_relat_1(esk11_0)=esk9_0)&k1_relat_1(esk12_0)=esk9_0)&k5_relat_1(esk10_0,esk11_0)=k5_relat_1(esk10_0,esk12_0))&esk11_0!=esk12_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.52  fof(c_0_9, plain, ![X38, X39, X40]:(((r2_hidden(X38,k1_relat_1(X40))|~r2_hidden(k4_tarski(X38,X39),X40)|(~v1_relat_1(X40)|~v1_funct_1(X40)))&(X39=k1_funct_1(X40,X38)|~r2_hidden(k4_tarski(X38,X39),X40)|(~v1_relat_1(X40)|~v1_funct_1(X40))))&(~r2_hidden(X38,k1_relat_1(X40))|X39!=k1_funct_1(X40,X38)|r2_hidden(k4_tarski(X38,X39),X40)|(~v1_relat_1(X40)|~v1_funct_1(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.52  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|X1=X2|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.52  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_13, negated_conjecture, (k1_relat_1(esk12_0)=esk9_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_14, negated_conjecture, (esk9_0=k2_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  fof(c_0_15, plain, ![X35, X36, X37]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~v1_relat_1(X37)|~v1_funct_1(X37)|(~r2_hidden(X35,k1_relat_1(X36))|k1_funct_1(k5_relat_1(X36,X37),X35)=k1_funct_1(X37,k1_funct_1(X36,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.19/0.52  cnf(c_0_16, negated_conjecture, (X1=esk11_0|r2_hidden(k4_tarski(esk1_2(X1,esk11_0),esk2_2(X1,esk11_0)),esk11_0)|r2_hidden(k4_tarski(esk1_2(X1,esk11_0),esk2_2(X1,esk11_0)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.19/0.52  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_18, negated_conjecture, (esk11_0!=esk12_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_12])).
% 0.19/0.52  cnf(c_0_20, negated_conjecture, (k1_relat_1(esk12_0)=k2_relat_1(esk10_0)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.52  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_22, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.52  cnf(c_0_23, negated_conjecture, (k5_relat_1(esk10_0,esk11_0)=k5_relat_1(esk10_0,esk12_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  fof(c_0_26, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X26),X24)|X25!=k2_relat_1(X24))&(~r2_hidden(k4_tarski(X29,X28),X24)|r2_hidden(X28,X25)|X25!=k2_relat_1(X24)))&((~r2_hidden(esk7_2(X30,X31),X31)|~r2_hidden(k4_tarski(X33,esk7_2(X30,X31)),X30)|X31=k2_relat_1(X30))&(r2_hidden(esk7_2(X30,X31),X31)|r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)|X31=k2_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.52  fof(c_0_27, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:(((~r2_hidden(X15,X14)|r2_hidden(k4_tarski(X15,esk3_3(X13,X14,X15)),X13)|X14!=k1_relat_1(X13))&(~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(X17,X14)|X14!=k1_relat_1(X13)))&((~r2_hidden(esk4_2(X19,X20),X20)|~r2_hidden(k4_tarski(esk4_2(X19,X20),X22),X19)|X20=k1_relat_1(X19))&(r2_hidden(esk4_2(X19,X20),X20)|r2_hidden(k4_tarski(esk4_2(X19,X20),esk5_2(X19,X20)),X19)|X20=k1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.19/0.52  cnf(c_0_28, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.52  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk12_0)|r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk11_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.19/0.52  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk12_0,X1)),esk12_0)|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_17])])).
% 0.19/0.52  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk12_0,k1_funct_1(esk10_0,X1))=k1_funct_1(k5_relat_1(esk10_0,esk11_0),X1)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_21]), c_0_24]), c_0_17]), c_0_25])])).
% 0.19/0.52  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.52  cnf(c_0_33, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.52  cnf(c_0_34, negated_conjecture, (esk2_2(esk12_0,esk11_0)=k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0))|r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_21]), c_0_17])])).
% 0.19/0.52  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk10_0,X1),k1_funct_1(k5_relat_1(esk10_0,esk11_0),X1)),esk12_0)|~r2_hidden(k1_funct_1(esk10_0,X1),k2_relat_1(esk10_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.52  cnf(c_0_37, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.52  cnf(c_0_38, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.52  cnf(c_0_39, negated_conjecture, (esk2_2(esk12_0,esk11_0)=k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0))|esk2_2(esk12_0,esk11_0)=k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_34]), c_0_35]), c_0_11])])).
% 0.19/0.52  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk10_0,X1),k1_funct_1(esk11_0,k1_funct_1(esk10_0,X1))),esk12_0)|~r2_hidden(k1_funct_1(esk10_0,X1),k2_relat_1(esk10_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_22]), c_0_35]), c_0_24]), c_0_11]), c_0_25])])).
% 0.19/0.52  cnf(c_0_41, plain, (k1_funct_1(X1,esk6_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_37])).
% 0.19/0.52  cnf(c_0_42, plain, (r2_hidden(esk6_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.19/0.52  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk11_0)=esk9_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.52  cnf(c_0_44, plain, (X1=X2|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.52  cnf(c_0_45, negated_conjecture, (esk2_2(esk12_0,esk11_0)=k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))|k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0))!=k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))), inference(ef,[status(thm)],[c_0_39])).
% 0.19/0.52  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk11_0,X1)),esk12_0)|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_24]), c_0_25])]), c_0_42])).
% 0.19/0.52  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),esk2_2(esk12_0,esk11_0)),esk11_0)|r2_hidden(esk1_2(esk12_0,esk11_0),k2_relat_1(esk10_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_29]), c_0_20])).
% 0.19/0.52  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk11_0)=k2_relat_1(esk10_0)), inference(rw,[status(thm)],[c_0_43, c_0_14])).
% 0.19/0.52  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk12_0,esk1_2(esk12_0,esk11_0))!=k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))|~r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk11_0)|~r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk12_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_11]), c_0_17])]), c_0_18])).
% 0.19/0.52  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk12_0,X1)=k1_funct_1(esk11_0,X1)|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_46]), c_0_21]), c_0_17])])).
% 0.19/0.52  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(esk12_0,esk11_0),k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_47]), c_0_48])])).
% 0.19/0.52  cnf(c_0_52, negated_conjecture, (~r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk11_0)|~r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk12_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.19/0.52  cnf(c_0_53, negated_conjecture, (~r2_hidden(k4_tarski(esk1_2(esk12_0,esk11_0),k1_funct_1(esk11_0,esk1_2(esk12_0,esk11_0))),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_51])])).
% 0.19/0.52  cnf(c_0_54, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk11_0,X1)),esk11_0)|~r2_hidden(X1,k2_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_48]), c_0_35]), c_0_11])])).
% 0.19/0.52  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_51])]), ['proof']).
% 0.19/0.52  # SZS output end CNFRefutation
% 0.19/0.52  # Proof object total steps             : 56
% 0.19/0.52  # Proof object clause steps            : 43
% 0.19/0.52  # Proof object formula steps           : 13
% 0.19/0.52  # Proof object conjectures             : 34
% 0.19/0.52  # Proof object clause conjectures      : 31
% 0.19/0.52  # Proof object formula conjectures     : 3
% 0.19/0.52  # Proof object initial clauses used    : 18
% 0.19/0.52  # Proof object initial formulas used   : 6
% 0.19/0.52  # Proof object generating inferences   : 20
% 0.19/0.52  # Proof object simplifying inferences  : 48
% 0.19/0.52  # Training examples: 0 positive, 0 negative
% 0.19/0.52  # Parsed axioms                        : 6
% 0.19/0.52  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.52  # Initial clauses                      : 27
% 0.19/0.52  # Removed in clause preprocessing      : 2
% 0.19/0.52  # Initial clauses in saturation        : 25
% 0.19/0.52  # Processed clauses                    : 758
% 0.19/0.52  # ...of these trivial                  : 0
% 0.19/0.52  # ...subsumed                          : 109
% 0.19/0.52  # ...remaining for further processing  : 649
% 0.19/0.52  # Other redundant clauses eliminated   : 5
% 0.19/0.52  # Clauses deleted for lack of memory   : 0
% 0.19/0.52  # Backward-subsumed                    : 19
% 0.19/0.52  # Backward-rewritten                   : 12
% 0.19/0.52  # Generated clauses                    : 4903
% 0.19/0.52  # ...of the previous two non-trivial   : 4826
% 0.19/0.52  # Contextual simplify-reflections      : 18
% 0.19/0.52  # Paramodulations                      : 4874
% 0.19/0.52  # Factorizations                       : 20
% 0.19/0.52  # Equation resolutions                 : 5
% 0.19/0.52  # Propositional unsat checks           : 0
% 0.19/0.52  #    Propositional check models        : 0
% 0.19/0.52  #    Propositional check unsatisfiable : 0
% 0.19/0.52  #    Propositional clauses             : 0
% 0.19/0.52  #    Propositional clauses after purity: 0
% 0.19/0.52  #    Propositional unsat core size     : 0
% 0.19/0.52  #    Propositional preprocessing time  : 0.000
% 0.19/0.52  #    Propositional encoding time       : 0.000
% 0.19/0.52  #    Propositional solver time         : 0.000
% 0.19/0.52  #    Success case prop preproc time    : 0.000
% 0.19/0.52  #    Success case prop encoding time   : 0.000
% 0.19/0.52  #    Success case prop solver time     : 0.000
% 0.19/0.52  # Current number of processed clauses  : 585
% 0.19/0.52  #    Positive orientable unit clauses  : 16
% 0.19/0.52  #    Positive unorientable unit clauses: 0
% 0.19/0.52  #    Negative unit clauses             : 2
% 0.19/0.52  #    Non-unit-clauses                  : 567
% 0.19/0.52  # Current number of unprocessed clauses: 4080
% 0.19/0.52  # ...number of literals in the above   : 18616
% 0.19/0.52  # Current number of archived formulas  : 0
% 0.19/0.52  # Current number of archived clauses   : 59
% 0.19/0.52  # Clause-clause subsumption calls (NU) : 120722
% 0.19/0.52  # Rec. Clause-clause subsumption calls : 72751
% 0.19/0.52  # Non-unit clause-clause subsumptions  : 146
% 0.19/0.52  # Unit Clause-clause subsumption calls : 98
% 0.19/0.52  # Rewrite failures with RHS unbound    : 0
% 0.19/0.52  # BW rewrite match attempts            : 8
% 0.19/0.52  # BW rewrite match successes           : 6
% 0.19/0.52  # Condensation attempts                : 0
% 0.19/0.52  # Condensation successes               : 0
% 0.19/0.52  # Termbank termtop insertions          : 180218
% 0.19/0.52  
% 0.19/0.52  # -------------------------------------------------
% 0.19/0.52  # User time                : 0.165 s
% 0.19/0.52  # System time              : 0.016 s
% 0.19/0.52  # Total time               : 0.182 s
% 0.19/0.52  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
