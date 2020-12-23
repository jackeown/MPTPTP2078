%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:13 EST 2020

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   81 (1445 expanded)
%              Number of clauses        :   66 ( 646 expanded)
%              Number of leaves         :    7 ( 385 expanded)
%              Depth                    :   24
%              Number of atoms          :  278 (6872 expanded)
%              Number of equality atoms :  117 (2438 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

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

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(c_0_7,plain,(
    ! [X45,X46,X48] :
      ( v1_relat_1(esk12_2(X45,X46))
      & v1_funct_1(esk12_2(X45,X46))
      & k1_relat_1(esk12_2(X45,X46)) = X45
      & ( ~ r2_hidden(X48,X45)
        | k1_funct_1(esk12_2(X45,X46),X48) = X46 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_8,plain,(
    ! [X35,X36,X37,X39,X40,X41,X43] :
      ( ( r2_hidden(esk9_3(X35,X36,X37),k1_relat_1(X35))
        | ~ r2_hidden(X37,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X37 = k1_funct_1(X35,esk9_3(X35,X36,X37))
        | ~ r2_hidden(X37,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X40,k1_relat_1(X35))
        | X39 != k1_funct_1(X35,X40)
        | r2_hidden(X39,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(esk10_2(X35,X41),X41)
        | ~ r2_hidden(X43,k1_relat_1(X35))
        | esk10_2(X35,X41) != k1_funct_1(X35,X43)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk11_2(X35,X41),k1_relat_1(X35))
        | r2_hidden(esk10_2(X35,X41),X41)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( esk10_2(X35,X41) = k1_funct_1(X35,esk11_2(X35,X41))
        | r2_hidden(esk10_2(X35,X41),X41)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_9,plain,
    ( k1_funct_1(esk12_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( X1 = k1_funct_1(X2,esk9_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( v1_funct_1(esk12_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(esk12_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k1_relat_1(esk12_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( X1 = X2
    | X3 != k2_relat_1(esk12_2(X4,X2))
    | ~ r2_hidden(esk9_3(esk12_2(X4,X2),X3,X1),X4)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk9_3(esk12_2(X1,X2),X3,X4),X1)
    | X3 != k2_relat_1(esk12_2(X1,X2))
    | ~ r2_hidden(X4,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_11]),c_0_12])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | X3 != k2_relat_1(esk12_2(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_relat_1(esk12_2(X3,X2))) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_23,plain,(
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

fof(c_0_24,plain,(
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

fof(c_0_25,negated_conjecture,(
    ! [X51] :
      ( ( esk13_0 != k1_xboole_0
        | esk14_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X51)
        | ~ v1_funct_1(X51)
        | esk14_0 != k1_relat_1(X51)
        | ~ r1_tarski(k2_relat_1(X51),esk13_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( esk1_2(k2_relat_1(esk12_2(X1,X2)),X3) = X2
    | r1_tarski(k2_relat_1(esk12_2(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_relat_1(esk12_2(X3,X1))
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_9]),c_0_11]),c_0_12]),c_0_14])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk14_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_relat_1(esk12_2(X1,X2)),X3)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_33,plain,(
    ! [X11] :
      ( X11 = k1_xboole_0
      | r2_hidden(esk2_1(X11),X11) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | ~ r2_hidden(X3,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X4)
    | X4 != k1_relat_1(X1)
    | X2 != k2_relat_1(X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( esk14_0 != X1
    | ~ r2_hidden(X2,esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14]),c_0_11]),c_0_12])])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | X3 != k2_relat_1(esk12_2(X2,X4))
    | ~ r2_hidden(X5,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_16])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | X2 != k1_relat_1(X3)
    | X4 != k2_relat_1(X3)
    | ~ r2_hidden(X5,X4) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( esk13_0 = k1_xboole_0
    | esk14_0 != X1 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | ~ r2_hidden(X3,k2_relat_1(esk12_2(X2,X4))) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(esk12_2(X3,X2)))
    | X3 != k1_relat_1(X4)
    | X1 != k2_relat_1(X4) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( esk14_0 = k1_xboole_0
    | esk13_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( esk13_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | X3 != k2_relat_1(k2_relat_1(esk12_2(X2,X4)))
    | ~ r2_hidden(X5,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(esk12_2(k1_relat_1(X3),X2)))
    | X1 != k2_relat_1(X3) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( esk14_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | ~ r2_hidden(X3,k2_relat_1(k2_relat_1(esk12_2(X2,X4)))) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(esk12_2(k1_relat_1(X1),X2))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k1_xboole_0 != X1
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_44]),c_0_47])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | X3 != k2_relat_1(esk12_2(k2_relat_1(k2_relat_1(esk12_2(X2,X4))),X5))
    | ~ r2_hidden(X6,X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_16])).

cnf(c_0_52,plain,
    ( k2_relat_1(esk12_2(X1,X2)) = k1_xboole_0
    | r2_hidden(X3,k2_relat_1(esk12_2(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( X1 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != X2
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_30])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | ~ r2_hidden(X3,k2_relat_1(esk12_2(k2_relat_1(k2_relat_1(esk12_2(X2,X4))),X5))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | esk14_0 != X2
    | ~ r1_tarski(k1_xboole_0,esk13_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_52]),c_0_14]),c_0_11]),c_0_12])])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k1_xboole_0
    | X1 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != X2 ),
    inference(spm,[status(thm)],[c_0_53,c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | k2_relat_1(k2_relat_1(esk12_2(X2,X3))) != esk14_0
    | ~ r1_tarski(k1_xboole_0,esk13_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | esk14_0 != k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,esk13_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_52]),c_0_41])).

cnf(c_0_60,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(X1,X2)
    | X2 != k1_relat_1(k2_relat_1(esk12_2(X3,k4_tarski(X1,X4))))
    | esk14_0 != k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,esk13_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1)
    | k1_xboole_0 != X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_60]),c_0_61])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | X3 != k1_relat_1(k2_relat_1(esk12_2(X2,X4)))
    | ~ r2_hidden(X5,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k2_relat_1(esk12_2(X2,k4_tarski(X1,X3)))))
    | esk14_0 != k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,esk13_0) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(X1) != k1_xboole_0
    | X2 != k2_relat_1(X1)
    | k1_xboole_0 != X3
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_35])).

cnf(c_0_69,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_2(k1_xboole_0,X1),X1) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))
    | ~ r2_hidden(X3,k1_relat_1(k2_relat_1(esk12_2(X2,X4)))) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(k2_relat_1(esk12_2(X2,k4_tarski(X1,X3))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_44]),c_0_67])]),c_0_47]),c_0_61])])).

cnf(c_0_72,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0
    | X1 != k2_relat_1(X2)
    | k1_xboole_0 != X3 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( X1 != k1_xboole_0
    | k1_xboole_0 != X2
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk12_2(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | k1_xboole_0 != X2 ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( k2_relat_1(esk12_2(X1,X2)) != k1_xboole_0
    | k1_xboole_0 != X3 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k1_xboole_0 != X1
    | X2 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_14])).

cnf(c_0_79,negated_conjecture,
    ( X1 != k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_44,c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:59:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.81/1.04  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.81/1.04  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.81/1.04  #
% 0.81/1.04  # Preprocessing time       : 0.028 s
% 0.81/1.04  # Presaturation interreduction done
% 0.81/1.04  
% 0.81/1.04  # Proof found!
% 0.81/1.04  # SZS status Theorem
% 0.81/1.04  # SZS output start CNFRefutation
% 0.81/1.04  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.81/1.04  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.81/1.04  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.81/1.04  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 0.81/1.04  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.81/1.04  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.81/1.04  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.81/1.04  fof(c_0_7, plain, ![X45, X46, X48]:(((v1_relat_1(esk12_2(X45,X46))&v1_funct_1(esk12_2(X45,X46)))&k1_relat_1(esk12_2(X45,X46))=X45)&(~r2_hidden(X48,X45)|k1_funct_1(esk12_2(X45,X46),X48)=X46)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.81/1.04  fof(c_0_8, plain, ![X35, X36, X37, X39, X40, X41, X43]:((((r2_hidden(esk9_3(X35,X36,X37),k1_relat_1(X35))|~r2_hidden(X37,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(X37=k1_funct_1(X35,esk9_3(X35,X36,X37))|~r2_hidden(X37,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X40,k1_relat_1(X35))|X39!=k1_funct_1(X35,X40)|r2_hidden(X39,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&((~r2_hidden(esk10_2(X35,X41),X41)|(~r2_hidden(X43,k1_relat_1(X35))|esk10_2(X35,X41)!=k1_funct_1(X35,X43))|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&((r2_hidden(esk11_2(X35,X41),k1_relat_1(X35))|r2_hidden(esk10_2(X35,X41),X41)|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(esk10_2(X35,X41)=k1_funct_1(X35,esk11_2(X35,X41))|r2_hidden(esk10_2(X35,X41),X41)|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.81/1.04  cnf(c_0_9, plain, (k1_funct_1(esk12_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.81/1.04  cnf(c_0_10, plain, (X1=k1_funct_1(X2,esk9_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.81/1.04  cnf(c_0_11, plain, (v1_funct_1(esk12_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.81/1.04  cnf(c_0_12, plain, (v1_relat_1(esk12_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.81/1.04  cnf(c_0_13, plain, (r2_hidden(esk9_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.81/1.04  cnf(c_0_14, plain, (k1_relat_1(esk12_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.81/1.04  cnf(c_0_15, plain, (X1=X2|X3!=k2_relat_1(esk12_2(X4,X2))|~r2_hidden(esk9_3(esk12_2(X4,X2),X3,X1),X4)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])])).
% 0.81/1.04  cnf(c_0_16, plain, (r2_hidden(esk9_3(esk12_2(X1,X2),X3,X4),X1)|X3!=k2_relat_1(esk12_2(X1,X2))|~r2_hidden(X4,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_11]), c_0_12])])).
% 0.81/1.04  cnf(c_0_17, plain, (X1=X2|X3!=k2_relat_1(esk12_2(X4,X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.81/1.04  fof(c_0_18, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.81/1.04  fof(c_0_19, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.81/1.04  cnf(c_0_20, plain, (X1=X2|~r2_hidden(X1,k2_relat_1(esk12_2(X3,X2)))), inference(er,[status(thm)],[c_0_17])).
% 0.81/1.04  cnf(c_0_21, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.81/1.04  cnf(c_0_22, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.81/1.04  fof(c_0_23, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:(((~r2_hidden(X15,X14)|r2_hidden(k4_tarski(X15,esk3_3(X13,X14,X15)),X13)|X14!=k1_relat_1(X13))&(~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(X17,X14)|X14!=k1_relat_1(X13)))&((~r2_hidden(esk4_2(X19,X20),X20)|~r2_hidden(k4_tarski(esk4_2(X19,X20),X22),X19)|X20=k1_relat_1(X19))&(r2_hidden(esk4_2(X19,X20),X20)|r2_hidden(k4_tarski(esk4_2(X19,X20),esk5_2(X19,X20)),X19)|X20=k1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.81/1.04  fof(c_0_24, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X26),X24)|X25!=k2_relat_1(X24))&(~r2_hidden(k4_tarski(X29,X28),X24)|r2_hidden(X28,X25)|X25!=k2_relat_1(X24)))&((~r2_hidden(esk7_2(X30,X31),X31)|~r2_hidden(k4_tarski(X33,esk7_2(X30,X31)),X30)|X31=k2_relat_1(X30))&(r2_hidden(esk7_2(X30,X31),X31)|r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)|X31=k2_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.81/1.04  fof(c_0_25, negated_conjecture, ![X51]:((esk13_0!=k1_xboole_0|esk14_0=k1_xboole_0)&(~v1_relat_1(X51)|~v1_funct_1(X51)|(esk14_0!=k1_relat_1(X51)|~r1_tarski(k2_relat_1(X51),esk13_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 0.81/1.04  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.81/1.04  cnf(c_0_27, plain, (esk1_2(k2_relat_1(esk12_2(X1,X2)),X3)=X2|r1_tarski(k2_relat_1(esk12_2(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.81/1.04  cnf(c_0_28, plain, (r2_hidden(X1,X2)|X2!=k2_relat_1(esk12_2(X3,X1))|~r2_hidden(X4,X3)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_9]), c_0_11]), c_0_12]), c_0_14])])])).
% 0.81/1.04  cnf(c_0_29, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.81/1.04  cnf(c_0_30, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.81/1.04  cnf(c_0_31, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk14_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk13_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.81/1.04  cnf(c_0_32, plain, (r1_tarski(k2_relat_1(esk12_2(X1,X2)),X3)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.81/1.04  fof(c_0_33, plain, ![X11]:(X11=k1_xboole_0|r2_hidden(esk2_1(X11),X11)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.81/1.04  cnf(c_0_34, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|~r2_hidden(X3,X2)), inference(er,[status(thm)],[c_0_28])).
% 0.81/1.04  cnf(c_0_35, plain, (r2_hidden(esk6_3(X1,X2,X3),X4)|X4!=k1_relat_1(X1)|X2!=k2_relat_1(X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.81/1.04  cnf(c_0_36, negated_conjecture, (esk14_0!=X1|~r2_hidden(X2,esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_14]), c_0_11]), c_0_12])])).
% 0.81/1.04  cnf(c_0_37, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.81/1.04  cnf(c_0_38, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|X3!=k2_relat_1(esk12_2(X2,X4))|~r2_hidden(X5,X3)), inference(spm,[status(thm)],[c_0_34, c_0_16])).
% 0.81/1.04  cnf(c_0_39, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|X2!=k1_relat_1(X3)|X4!=k2_relat_1(X3)|~r2_hidden(X5,X4)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.81/1.04  cnf(c_0_40, negated_conjecture, (esk13_0=k1_xboole_0|esk14_0!=X1), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.81/1.04  cnf(c_0_41, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|~r2_hidden(X3,k2_relat_1(esk12_2(X2,X4)))), inference(er,[status(thm)],[c_0_38])).
% 0.81/1.04  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(X2,k2_relat_1(esk12_2(X3,X2)))|X3!=k1_relat_1(X4)|X1!=k2_relat_1(X4)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.81/1.04  cnf(c_0_43, negated_conjecture, (esk14_0=k1_xboole_0|esk13_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.81/1.04  cnf(c_0_44, negated_conjecture, (esk13_0=k1_xboole_0), inference(er,[status(thm)],[c_0_40])).
% 0.81/1.04  cnf(c_0_45, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|X3!=k2_relat_1(k2_relat_1(esk12_2(X2,X4)))|~r2_hidden(X5,X3)), inference(spm,[status(thm)],[c_0_41, c_0_30])).
% 0.81/1.04  cnf(c_0_46, plain, (X1=k1_xboole_0|r2_hidden(X2,k2_relat_1(esk12_2(k1_relat_1(X3),X2)))|X1!=k2_relat_1(X3)), inference(er,[status(thm)],[c_0_42])).
% 0.81/1.04  cnf(c_0_47, negated_conjecture, (esk14_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.81/1.04  cnf(c_0_48, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|~r2_hidden(X3,k2_relat_1(k2_relat_1(esk12_2(X2,X4))))), inference(er,[status(thm)],[c_0_45])).
% 0.81/1.04  cnf(c_0_49, plain, (k2_relat_1(X1)=k1_xboole_0|r2_hidden(X2,k2_relat_1(esk12_2(k1_relat_1(X1),X2)))), inference(er,[status(thm)],[c_0_46])).
% 0.81/1.04  cnf(c_0_50, negated_conjecture, (k1_xboole_0!=X1|~r2_hidden(X2,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_44]), c_0_47])).
% 0.81/1.04  cnf(c_0_51, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|X3!=k2_relat_1(esk12_2(k2_relat_1(k2_relat_1(esk12_2(X2,X4))),X5))|~r2_hidden(X6,X3)), inference(spm,[status(thm)],[c_0_48, c_0_16])).
% 0.81/1.04  cnf(c_0_52, plain, (k2_relat_1(esk12_2(X1,X2))=k1_xboole_0|r2_hidden(X3,k2_relat_1(esk12_2(X1,X3)))), inference(spm,[status(thm)],[c_0_49, c_0_14])).
% 0.81/1.04  cnf(c_0_53, negated_conjecture, (X1!=k2_relat_1(k1_xboole_0)|k1_xboole_0!=X2|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_50, c_0_30])).
% 0.81/1.04  cnf(c_0_54, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|~r2_hidden(X3,k2_relat_1(esk12_2(k2_relat_1(k2_relat_1(esk12_2(X2,X4))),X5)))), inference(er,[status(thm)],[c_0_51])).
% 0.81/1.04  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|esk14_0!=X2|~r1_tarski(k1_xboole_0,esk13_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_52]), c_0_14]), c_0_11]), c_0_12])])).
% 0.81/1.04  cnf(c_0_56, negated_conjecture, (X1=k1_xboole_0|X1!=k2_relat_1(k1_xboole_0)|k1_xboole_0!=X2), inference(spm,[status(thm)],[c_0_53, c_0_37])).
% 0.81/1.04  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|k2_relat_1(k2_relat_1(esk12_2(X2,X3)))!=esk14_0|~r1_tarski(k1_xboole_0,esk13_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.81/1.04  cnf(c_0_58, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0|k1_xboole_0!=X1), inference(er,[status(thm)],[c_0_56])).
% 0.81/1.04  cnf(c_0_59, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|esk14_0!=k2_relat_1(k1_xboole_0)|~r1_tarski(k1_xboole_0,esk13_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_52]), c_0_41])).
% 0.81/1.04  cnf(c_0_60, plain, (r2_hidden(esk7_2(X1,X2),X2)|r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.81/1.04  cnf(c_0_61, negated_conjecture, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_58])).
% 0.81/1.04  cnf(c_0_62, plain, (r2_hidden(k4_tarski(X1,esk3_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.81/1.04  cnf(c_0_63, negated_conjecture, (r2_hidden(X1,X2)|X2!=k1_relat_1(k2_relat_1(esk12_2(X3,k4_tarski(X1,X4))))|esk14_0!=k2_relat_1(k1_xboole_0)|~r1_tarski(k1_xboole_0,esk13_0)), inference(spm,[status(thm)],[c_0_29, c_0_59])).
% 0.81/1.04  cnf(c_0_64, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk7_2(k1_xboole_0,X1),X1)|k1_xboole_0!=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_60]), c_0_61])).
% 0.81/1.04  cnf(c_0_65, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|X3!=k1_relat_1(k2_relat_1(esk12_2(X2,X4)))|~r2_hidden(X5,X3)), inference(spm,[status(thm)],[c_0_41, c_0_62])).
% 0.81/1.04  cnf(c_0_66, negated_conjecture, (r2_hidden(X1,k1_relat_1(k2_relat_1(esk12_2(X2,k4_tarski(X1,X3)))))|esk14_0!=k2_relat_1(k1_xboole_0)|~r1_tarski(k1_xboole_0,esk13_0)), inference(er,[status(thm)],[c_0_63])).
% 0.81/1.04  cnf(c_0_67, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.81/1.04  cnf(c_0_68, negated_conjecture, (k1_relat_1(X1)!=k1_xboole_0|X2!=k2_relat_1(X1)|k1_xboole_0!=X3|~r2_hidden(X4,X2)), inference(spm,[status(thm)],[c_0_50, c_0_35])).
% 0.81/1.04  cnf(c_0_69, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk7_2(k1_xboole_0,X1),X1)), inference(er,[status(thm)],[c_0_64])).
% 0.81/1.04  cnf(c_0_70, plain, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))|~r2_hidden(X3,k1_relat_1(k2_relat_1(esk12_2(X2,X4))))), inference(er,[status(thm)],[c_0_65])).
% 0.81/1.04  cnf(c_0_71, negated_conjecture, (r2_hidden(X1,k1_relat_1(k2_relat_1(esk12_2(X2,k4_tarski(X1,X3)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_44]), c_0_67])]), c_0_47]), c_0_61])])).
% 0.81/1.04  cnf(c_0_72, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(X2)!=k1_xboole_0|X1!=k2_relat_1(X2)|k1_xboole_0!=X3), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.81/1.04  cnf(c_0_73, negated_conjecture, (X1!=k1_xboole_0|k1_xboole_0!=X2|~r2_hidden(X3,X1)), inference(rw,[status(thm)],[c_0_53, c_0_61])).
% 0.81/1.04  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk12_2(X2,X1)))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.81/1.04  cnf(c_0_75, negated_conjecture, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|k1_xboole_0!=X2), inference(er,[status(thm)],[c_0_72])).
% 0.81/1.04  cnf(c_0_76, negated_conjecture, (k2_relat_1(esk12_2(X1,X2))!=k1_xboole_0|k1_xboole_0!=X3), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.81/1.04  cnf(c_0_77, negated_conjecture, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0), inference(er,[status(thm)],[c_0_75])).
% 0.81/1.04  cnf(c_0_78, negated_conjecture, (k1_xboole_0!=X1|X2!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_14])).
% 0.81/1.04  cnf(c_0_79, negated_conjecture, (X1!=k1_xboole_0), inference(er,[status(thm)],[c_0_78])).
% 0.81/1.04  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_44, c_0_79]), ['proof']).
% 0.81/1.04  # SZS output end CNFRefutation
% 0.81/1.04  # Proof object total steps             : 81
% 0.81/1.04  # Proof object clause steps            : 66
% 0.81/1.04  # Proof object formula steps           : 15
% 0.81/1.04  # Proof object conjectures             : 32
% 0.81/1.04  # Proof object clause conjectures      : 29
% 0.81/1.04  # Proof object formula conjectures     : 3
% 0.81/1.04  # Proof object initial clauses used    : 16
% 0.81/1.04  # Proof object initial formulas used   : 7
% 0.81/1.04  # Proof object generating inferences   : 45
% 0.81/1.04  # Proof object simplifying inferences  : 34
% 0.81/1.04  # Training examples: 0 positive, 0 negative
% 0.81/1.04  # Parsed axioms                        : 7
% 0.81/1.04  # Removed by relevancy pruning/SinE    : 0
% 0.81/1.04  # Initial clauses                      : 24
% 0.81/1.04  # Removed in clause preprocessing      : 0
% 0.81/1.04  # Initial clauses in saturation        : 24
% 0.81/1.04  # Processed clauses                    : 2051
% 0.81/1.04  # ...of these trivial                  : 6
% 0.81/1.04  # ...subsumed                          : 455
% 0.81/1.04  # ...remaining for further processing  : 1590
% 0.81/1.04  # Other redundant clauses eliminated   : 310
% 0.81/1.04  # Clauses deleted for lack of memory   : 0
% 0.81/1.04  # Backward-subsumed                    : 255
% 0.81/1.04  # Backward-rewritten                   : 1184
% 0.81/1.04  # Generated clauses                    : 54227
% 0.81/1.04  # ...of the previous two non-trivial   : 53937
% 0.81/1.04  # Contextual simplify-reflections      : 6
% 0.81/1.04  # Paramodulations                      : 53063
% 0.81/1.04  # Factorizations                       : 0
% 0.81/1.04  # Equation resolutions                 : 1157
% 0.81/1.04  # Propositional unsat checks           : 0
% 0.81/1.04  #    Propositional check models        : 0
% 0.81/1.04  #    Propositional check unsatisfiable : 0
% 0.81/1.04  #    Propositional clauses             : 0
% 0.81/1.04  #    Propositional clauses after purity: 0
% 0.81/1.04  #    Propositional unsat core size     : 0
% 0.81/1.04  #    Propositional preprocessing time  : 0.000
% 0.81/1.04  #    Propositional encoding time       : 0.000
% 0.81/1.04  #    Propositional solver time         : 0.000
% 0.81/1.04  #    Success case prop preproc time    : 0.000
% 0.81/1.04  #    Success case prop encoding time   : 0.000
% 0.81/1.04  #    Success case prop solver time     : 0.000
% 0.81/1.04  # Current number of processed clauses  : 120
% 0.81/1.04  #    Positive orientable unit clauses  : 8
% 0.81/1.04  #    Positive unorientable unit clauses: 0
% 0.81/1.04  #    Negative unit clauses             : 2
% 0.81/1.04  #    Non-unit-clauses                  : 110
% 0.81/1.04  # Current number of unprocessed clauses: 51248
% 0.81/1.04  # ...number of literals in the above   : 228447
% 0.81/1.04  # Current number of archived formulas  : 0
% 0.81/1.04  # Current number of archived clauses   : 1470
% 0.81/1.04  # Clause-clause subsumption calls (NU) : 207100
% 0.81/1.04  # Rec. Clause-clause subsumption calls : 134355
% 0.81/1.04  # Non-unit clause-clause subsumptions  : 479
% 0.81/1.04  # Unit Clause-clause subsumption calls : 3120
% 0.81/1.04  # Rewrite failures with RHS unbound    : 0
% 0.81/1.04  # BW rewrite match attempts            : 53
% 0.81/1.04  # BW rewrite match successes           : 35
% 0.81/1.04  # Condensation attempts                : 0
% 0.81/1.04  # Condensation successes               : 0
% 0.81/1.04  # Termbank termtop insertions          : 890821
% 0.81/1.04  
% 0.81/1.04  # -------------------------------------------------
% 0.81/1.04  # User time                : 0.658 s
% 0.81/1.04  # System time              : 0.028 s
% 0.81/1.04  # Total time               : 0.687 s
% 0.81/1.04  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
