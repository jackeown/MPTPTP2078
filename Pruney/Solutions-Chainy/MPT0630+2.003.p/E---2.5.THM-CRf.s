%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:18 EST 2020

% Result     : Theorem 36.46s
% Output     : CNFRefutation 36.46s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 224 expanded)
%              Number of clauses        :   36 (  96 expanded)
%              Number of leaves         :    7 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  214 (1089 expanded)
%              Number of equality atoms :   35 ( 194 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t27_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
           => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk2_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk3_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(esk5_3(X24,X25,X26),X26),X24)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(esk6_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk6_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) )
      & ( r2_hidden(esk6_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( k1_relat_1(k5_relat_1(X2,X1)) = k1_relat_1(X2)
             => r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t27_funct_1])).

fof(c_0_10,plain,(
    ! [X50,X51,X52] :
      ( ( r2_hidden(X50,k1_relat_1(X52))
        | ~ r2_hidden(k4_tarski(X50,X51),X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( X51 = k1_funct_1(X52,X50)
        | ~ r2_hidden(k4_tarski(X50,X51),X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( ~ r2_hidden(X50,k1_relat_1(X52))
        | X51 != k1_funct_1(X52,X50)
        | r2_hidden(k4_tarski(X50,X51),X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & v1_funct_1(esk12_0)
    & v1_relat_1(esk13_0)
    & v1_funct_1(esk13_0)
    & k1_relat_1(k5_relat_1(esk13_0,esk12_0)) = k1_relat_1(esk13_0)
    & ~ r1_tarski(k2_relat_1(esk13_0),k1_relat_1(esk12_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X35,X36,X37,X38,X39,X41,X42,X43,X46] :
      ( ( r2_hidden(k4_tarski(X38,esk8_5(X35,X36,X37,X38,X39)),X35)
        | ~ r2_hidden(k4_tarski(X38,X39),X37)
        | X37 != k5_relat_1(X35,X36)
        | ~ v1_relat_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(k4_tarski(esk8_5(X35,X36,X37,X38,X39),X39),X36)
        | ~ r2_hidden(k4_tarski(X38,X39),X37)
        | X37 != k5_relat_1(X35,X36)
        | ~ v1_relat_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(X41,X43),X35)
        | ~ r2_hidden(k4_tarski(X43,X42),X36)
        | r2_hidden(k4_tarski(X41,X42),X37)
        | X37 != k5_relat_1(X35,X36)
        | ~ v1_relat_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) )
      & ( ~ r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk10_3(X35,X36,X37)),X37)
        | ~ r2_hidden(k4_tarski(esk9_3(X35,X36,X37),X46),X35)
        | ~ r2_hidden(k4_tarski(X46,esk10_3(X35,X36,X37)),X36)
        | X37 = k5_relat_1(X35,X36)
        | ~ v1_relat_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk11_3(X35,X36,X37)),X35)
        | r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk10_3(X35,X36,X37)),X37)
        | X37 = k5_relat_1(X35,X36)
        | ~ v1_relat_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(k4_tarski(esk11_3(X35,X36,X37),esk10_3(X35,X36,X37)),X36)
        | r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk10_3(X35,X36,X37)),X37)
        | X37 = k5_relat_1(X35,X36)
        | ~ v1_relat_1(X37)
        | ~ v1_relat_1(X36)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_16,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X48)
      | ~ v1_relat_1(X49)
      | v1_relat_1(k5_relat_1(X48,X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk13_0),k1_relat_1(esk12_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,esk8_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk13_0,esk12_0)) = k1_relat_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_30,plain,
    ( k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)),k2_relat_1(esk13_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(esk8_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,esk8_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),k5_relat_1(esk13_0,esk12_0))
    | ~ r2_hidden(X1,k1_relat_1(esk13_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2))),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk13_0,esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)))) = esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk8_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1))),esk13_0)
    | ~ r2_hidden(X1,k1_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_33])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_39]),c_0_32]),c_0_33])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),esk12_0)
    | ~ r2_hidden(X1,k1_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_37]),c_0_33])])).

cnf(c_0_44,negated_conjecture,
    ( esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)) = k1_funct_1(esk13_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk13_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_41]),c_0_32]),c_0_33])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),k1_relat_1(esk13_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,k1_relat_1(esk13_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))))) = esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_39])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)),k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_45])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 36.46/36.63  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 36.46/36.63  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 36.46/36.63  #
% 36.46/36.63  # Preprocessing time       : 0.028 s
% 36.46/36.63  # Presaturation interreduction done
% 36.46/36.63  
% 36.46/36.63  # Proof found!
% 36.46/36.63  # SZS status Theorem
% 36.46/36.63  # SZS output start CNFRefutation
% 36.46/36.63  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 36.46/36.63  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 36.46/36.63  fof(t27_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(k5_relat_1(X2,X1))=k1_relat_1(X2)=>r1_tarski(k2_relat_1(X2),k1_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 36.46/36.63  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 36.46/36.63  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 36.46/36.63  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 36.46/36.63  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 36.46/36.63  fof(c_0_7, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:(((~r2_hidden(X15,X14)|r2_hidden(k4_tarski(X15,esk2_3(X13,X14,X15)),X13)|X14!=k1_relat_1(X13))&(~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(X17,X14)|X14!=k1_relat_1(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|~r2_hidden(k4_tarski(esk3_2(X19,X20),X22),X19)|X20=k1_relat_1(X19))&(r2_hidden(esk3_2(X19,X20),X20)|r2_hidden(k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)),X19)|X20=k1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 36.46/36.63  fof(c_0_8, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(esk5_3(X24,X25,X26),X26),X24)|X25!=k2_relat_1(X24))&(~r2_hidden(k4_tarski(X29,X28),X24)|r2_hidden(X28,X25)|X25!=k2_relat_1(X24)))&((~r2_hidden(esk6_2(X30,X31),X31)|~r2_hidden(k4_tarski(X33,esk6_2(X30,X31)),X30)|X31=k2_relat_1(X30))&(r2_hidden(esk6_2(X30,X31),X31)|r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X30)|X31=k2_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 36.46/36.63  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(k5_relat_1(X2,X1))=k1_relat_1(X2)=>r1_tarski(k2_relat_1(X2),k1_relat_1(X1)))))), inference(assume_negation,[status(cth)],[t27_funct_1])).
% 36.46/36.63  fof(c_0_10, plain, ![X50, X51, X52]:(((r2_hidden(X50,k1_relat_1(X52))|~r2_hidden(k4_tarski(X50,X51),X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(X51=k1_funct_1(X52,X50)|~r2_hidden(k4_tarski(X50,X51),X52)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(~r2_hidden(X50,k1_relat_1(X52))|X51!=k1_funct_1(X52,X50)|r2_hidden(k4_tarski(X50,X51),X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 36.46/36.63  cnf(c_0_11, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 36.46/36.63  cnf(c_0_12, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 36.46/36.63  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk12_0)&v1_funct_1(esk12_0))&((v1_relat_1(esk13_0)&v1_funct_1(esk13_0))&(k1_relat_1(k5_relat_1(esk13_0,esk12_0))=k1_relat_1(esk13_0)&~r1_tarski(k2_relat_1(esk13_0),k1_relat_1(esk12_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 36.46/36.63  fof(c_0_14, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 36.46/36.63  fof(c_0_15, plain, ![X35, X36, X37, X38, X39, X41, X42, X43, X46]:((((r2_hidden(k4_tarski(X38,esk8_5(X35,X36,X37,X38,X39)),X35)|~r2_hidden(k4_tarski(X38,X39),X37)|X37!=k5_relat_1(X35,X36)|~v1_relat_1(X37)|~v1_relat_1(X36)|~v1_relat_1(X35))&(r2_hidden(k4_tarski(esk8_5(X35,X36,X37,X38,X39),X39),X36)|~r2_hidden(k4_tarski(X38,X39),X37)|X37!=k5_relat_1(X35,X36)|~v1_relat_1(X37)|~v1_relat_1(X36)|~v1_relat_1(X35)))&(~r2_hidden(k4_tarski(X41,X43),X35)|~r2_hidden(k4_tarski(X43,X42),X36)|r2_hidden(k4_tarski(X41,X42),X37)|X37!=k5_relat_1(X35,X36)|~v1_relat_1(X37)|~v1_relat_1(X36)|~v1_relat_1(X35)))&((~r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk10_3(X35,X36,X37)),X37)|(~r2_hidden(k4_tarski(esk9_3(X35,X36,X37),X46),X35)|~r2_hidden(k4_tarski(X46,esk10_3(X35,X36,X37)),X36))|X37=k5_relat_1(X35,X36)|~v1_relat_1(X37)|~v1_relat_1(X36)|~v1_relat_1(X35))&((r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk11_3(X35,X36,X37)),X35)|r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk10_3(X35,X36,X37)),X37)|X37=k5_relat_1(X35,X36)|~v1_relat_1(X37)|~v1_relat_1(X36)|~v1_relat_1(X35))&(r2_hidden(k4_tarski(esk11_3(X35,X36,X37),esk10_3(X35,X36,X37)),X36)|r2_hidden(k4_tarski(esk9_3(X35,X36,X37),esk10_3(X35,X36,X37)),X37)|X37=k5_relat_1(X35,X36)|~v1_relat_1(X37)|~v1_relat_1(X36)|~v1_relat_1(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 36.46/36.63  fof(c_0_16, plain, ![X48, X49]:(~v1_relat_1(X48)|~v1_relat_1(X49)|v1_relat_1(k5_relat_1(X48,X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 36.46/36.63  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 36.46/36.63  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 36.46/36.63  cnf(c_0_19, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_11])).
% 36.46/36.63  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_12])).
% 36.46/36.63  cnf(c_0_21, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 36.46/36.63  cnf(c_0_22, negated_conjecture, (~r1_tarski(k2_relat_1(esk13_0),k1_relat_1(esk12_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 36.46/36.63  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 36.46/36.63  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,esk8_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 36.46/36.63  cnf(c_0_25, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 36.46/36.63  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_17])).
% 36.46/36.63  cnf(c_0_27, negated_conjecture, (k1_relat_1(k5_relat_1(esk13_0,esk12_0))=k1_relat_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 36.46/36.63  cnf(c_0_28, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_18])).
% 36.46/36.63  cnf(c_0_29, plain, (r2_hidden(esk5_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 36.46/36.63  cnf(c_0_30, plain, (k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 36.46/36.63  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)),k2_relat_1(esk13_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 36.46/36.63  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 36.46/36.63  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk13_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 36.46/36.63  cnf(c_0_34, plain, (r2_hidden(k4_tarski(esk8_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 36.46/36.63  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,esk8_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_25])).
% 36.46/36.63  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),k5_relat_1(esk13_0,esk12_0))|~r2_hidden(X1,k1_relat_1(esk13_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 36.46/36.63  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 36.46/36.63  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),k1_funct_1(X1,esk5_3(X1,k2_relat_1(X1),X2))),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 36.46/36.63  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk13_0,esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))))=esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 36.46/36.63  cnf(c_0_40, plain, (r2_hidden(k4_tarski(esk8_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_25])).
% 36.46/36.63  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(X1,esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1))),esk13_0)|~r2_hidden(X1,k1_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_33])])).
% 36.46/36.63  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_39]), c_0_32]), c_0_33])])).
% 36.46/36.63  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),esk12_0)|~r2_hidden(X1,k1_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_37]), c_0_33])])).
% 36.46/36.63  cnf(c_0_44, negated_conjecture, (esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1))=k1_funct_1(esk13_0,X1)|~r2_hidden(X1,k1_relat_1(esk13_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_41]), c_0_32]), c_0_33])])).
% 36.46/36.63  cnf(c_0_45, negated_conjecture, (r2_hidden(esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),k1_relat_1(esk13_0))), inference(spm,[status(thm)],[c_0_19, c_0_42])).
% 36.46/36.63  cnf(c_0_46, negated_conjecture, (r2_hidden(esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),X1,esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),X1)),k1_relat_1(esk12_0))|~r2_hidden(X1,k1_relat_1(esk13_0))), inference(spm,[status(thm)],[c_0_19, c_0_43])).
% 36.46/36.63  cnf(c_0_47, negated_conjecture, (esk8_5(esk13_0,esk12_0,k5_relat_1(esk13_0,esk12_0),esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))),esk2_3(k5_relat_1(esk13_0,esk12_0),k1_relat_1(esk13_0),esk5_3(esk13_0,k2_relat_1(esk13_0),esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)))))=esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_39])).
% 36.46/36.63  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 36.46/36.63  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk13_0),k1_relat_1(esk12_0)),k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_45])])).
% 36.46/36.63  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_22]), ['proof']).
% 36.46/36.63  # SZS output end CNFRefutation
% 36.46/36.63  # Proof object total steps             : 51
% 36.46/36.63  # Proof object clause steps            : 36
% 36.46/36.63  # Proof object formula steps           : 15
% 36.46/36.63  # Proof object conjectures             : 20
% 36.46/36.63  # Proof object clause conjectures      : 17
% 36.46/36.63  # Proof object formula conjectures     : 3
% 36.46/36.63  # Proof object initial clauses used    : 15
% 36.46/36.63  # Proof object initial formulas used   : 7
% 36.46/36.63  # Proof object generating inferences   : 15
% 36.46/36.63  # Proof object simplifying inferences  : 28
% 36.46/36.63  # Training examples: 0 positive, 0 negative
% 36.46/36.63  # Parsed axioms                        : 7
% 36.46/36.63  # Removed by relevancy pruning/SinE    : 0
% 36.46/36.63  # Initial clauses                      : 27
% 36.46/36.63  # Removed in clause preprocessing      : 0
% 36.46/36.63  # Initial clauses in saturation        : 27
% 36.46/36.63  # Processed clauses                    : 32787
% 36.46/36.63  # ...of these trivial                  : 1
% 36.46/36.63  # ...subsumed                          : 13178
% 36.46/36.63  # ...remaining for further processing  : 19608
% 36.46/36.63  # Other redundant clauses eliminated   : 8
% 36.46/36.63  # Clauses deleted for lack of memory   : 0
% 36.46/36.63  # Backward-subsumed                    : 1442
% 36.46/36.63  # Backward-rewritten                   : 49
% 36.46/36.63  # Generated clauses                    : 1751606
% 36.46/36.63  # ...of the previous two non-trivial   : 1747979
% 36.46/36.63  # Contextual simplify-reflections      : 153
% 36.46/36.63  # Paramodulations                      : 1750764
% 36.46/36.63  # Factorizations                       : 834
% 36.46/36.63  # Equation resolutions                 : 8
% 36.46/36.63  # Propositional unsat checks           : 0
% 36.46/36.63  #    Propositional check models        : 0
% 36.46/36.63  #    Propositional check unsatisfiable : 0
% 36.46/36.63  #    Propositional clauses             : 0
% 36.46/36.63  #    Propositional clauses after purity: 0
% 36.46/36.63  #    Propositional unsat core size     : 0
% 36.46/36.63  #    Propositional preprocessing time  : 0.000
% 36.46/36.63  #    Propositional encoding time       : 0.000
% 36.46/36.63  #    Propositional solver time         : 0.000
% 36.46/36.63  #    Success case prop preproc time    : 0.000
% 36.46/36.63  #    Success case prop encoding time   : 0.000
% 36.46/36.63  #    Success case prop solver time     : 0.000
% 36.46/36.63  # Current number of processed clauses  : 18083
% 36.46/36.63  #    Positive orientable unit clauses  : 13
% 36.46/36.63  #    Positive unorientable unit clauses: 0
% 36.46/36.63  #    Negative unit clauses             : 1
% 36.46/36.63  #    Non-unit-clauses                  : 18069
% 36.46/36.63  # Current number of unprocessed clauses: 1713601
% 36.46/36.63  # ...number of literals in the above   : 10314996
% 36.46/36.63  # Current number of archived formulas  : 0
% 36.46/36.63  # Current number of archived clauses   : 1517
% 36.46/36.63  # Clause-clause subsumption calls (NU) : 20266512
% 36.46/36.63  # Rec. Clause-clause subsumption calls : 662081
% 36.46/36.63  # Non-unit clause-clause subsumptions  : 14773
% 36.46/36.63  # Unit Clause-clause subsumption calls : 9770
% 36.46/36.63  # Rewrite failures with RHS unbound    : 0
% 36.46/36.63  # BW rewrite match attempts            : 306
% 36.46/36.63  # BW rewrite match successes           : 2
% 36.46/36.63  # Condensation attempts                : 0
% 36.46/36.63  # Condensation successes               : 0
% 36.46/36.63  # Termbank termtop insertions          : 84579676
% 36.52/36.74  
% 36.52/36.74  # -------------------------------------------------
% 36.52/36.74  # User time                : 35.600 s
% 36.52/36.74  # System time              : 0.796 s
% 36.52/36.74  # Total time               : 36.396 s
% 36.52/36.74  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
