%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:48 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 146 expanded)
%              Number of clauses        :   50 (  73 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  224 ( 592 expanded)
%              Number of equality atoms :   42 ( 112 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(t33_wellord2,conjecture,(
    ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(X37,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X39,X40,X41,X42] :
      ( ( k3_relat_1(X40) = X39
        | X40 != k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(X41,X42),X40)
        | r1_tarski(X41,X42)
        | ~ r2_hidden(X41,X39)
        | ~ r2_hidden(X42,X39)
        | X40 != k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r1_tarski(X41,X42)
        | r2_hidden(k4_tarski(X41,X42),X40)
        | ~ r2_hidden(X41,X39)
        | ~ r2_hidden(X42,X39)
        | X40 != k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk8_2(X39,X40),X39)
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk9_2(X39,X40),X39)
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(k4_tarski(esk8_2(X39,X40),esk9_2(X39,X40)),X40)
        | ~ r1_tarski(esk8_2(X39,X40),esk9_2(X39,X40))
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(k4_tarski(esk8_2(X39,X40),esk9_2(X39,X40)),X40)
        | r1_tarski(esk8_2(X39,X40),esk9_2(X39,X40))
        | k3_relat_1(X40) != X39
        | X40 = k1_wellord2(X39)
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_13,plain,(
    ! [X45] : v1_relat_1(k1_wellord2(X45)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_14,plain,(
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

cnf(c_0_15,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20])])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | r1_tarski(X35,k2_zfmisc_1(k1_relat_1(X35),k2_relat_1(X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(k1_relat_1(X1),X2),k3_relat_1(X1))
    | r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_20])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_relat_1(k1_wellord2(X2)))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_23])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(k1_relat_1(k1_wellord2(X1)),X2),X1)
    | r1_tarski(k1_relat_1(k1_wellord2(X1)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_20]),c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_relat_1(k1_wellord2(X2)))
    | r1_tarski(X2,X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,esk1_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(k2_relat_1(X1),X2),k3_relat_1(X1))
    | r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_23])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k2_relat_1(k1_wellord2(X2)))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(k1_wellord2(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(k1_wellord2(X1)))
    | r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_23])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(k2_relat_1(k1_wellord2(X1)),X2),X1)
    | r1_tarski(k2_relat_1(k1_wellord2(X1)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_34])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_relat_1(k1_wellord2(X1)))
    | r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(X3,esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_23])).

cnf(c_0_53,plain,
    ( r2_hidden(esk1_2(k1_wellord2(X1),X2),k2_zfmisc_1(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))))
    | r1_tarski(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_54,plain,
    ( k1_relat_1(k1_wellord2(X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k1_relat_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_relat_1(k1_wellord2(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_relat_1(k1_wellord2(X1)))
    | r1_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_44]),c_0_23])).

fof(c_0_58,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(assume_negation,[status(cth)],[t33_wellord2])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_53])).

cnf(c_0_60,plain,
    ( k1_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_61,plain,
    ( k2_relat_1(k1_wellord2(X1)) = X1
    | ~ r1_tarski(X1,k2_relat_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_56])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k2_relat_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57])).

fof(c_0_63,negated_conjecture,(
    ~ r1_tarski(k1_wellord2(esk10_0),k2_zfmisc_1(esk10_0,esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,k2_relat_1(k1_wellord2(X1)))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( k2_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tarski(k1_wellord2(esk10_0),k2_zfmisc_1(esk10_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:42:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.028 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.12/0.39  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 0.12/0.39  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.12/0.39  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.39  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.12/0.39  fof(t33_wellord2, conjecture, ![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 0.12/0.39  fof(c_0_9, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:(((~r2_hidden(X15,X14)|r2_hidden(k4_tarski(X15,esk2_3(X13,X14,X15)),X13)|X14!=k1_relat_1(X13))&(~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(X17,X14)|X14!=k1_relat_1(X13)))&((~r2_hidden(esk3_2(X19,X20),X20)|~r2_hidden(k4_tarski(esk3_2(X19,X20),X22),X19)|X20=k1_relat_1(X19))&(r2_hidden(esk3_2(X19,X20),X20)|r2_hidden(k4_tarski(esk3_2(X19,X20),esk4_2(X19,X20)),X19)|X20=k1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.12/0.39  fof(c_0_10, plain, ![X36, X37, X38]:((r2_hidden(X36,k3_relat_1(X38))|~r2_hidden(k4_tarski(X36,X37),X38)|~v1_relat_1(X38))&(r2_hidden(X37,k3_relat_1(X38))|~r2_hidden(k4_tarski(X36,X37),X38)|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.12/0.39  cnf(c_0_11, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  fof(c_0_12, plain, ![X39, X40, X41, X42]:(((k3_relat_1(X40)=X39|X40!=k1_wellord2(X39)|~v1_relat_1(X40))&((~r2_hidden(k4_tarski(X41,X42),X40)|r1_tarski(X41,X42)|(~r2_hidden(X41,X39)|~r2_hidden(X42,X39))|X40!=k1_wellord2(X39)|~v1_relat_1(X40))&(~r1_tarski(X41,X42)|r2_hidden(k4_tarski(X41,X42),X40)|(~r2_hidden(X41,X39)|~r2_hidden(X42,X39))|X40!=k1_wellord2(X39)|~v1_relat_1(X40))))&(((r2_hidden(esk8_2(X39,X40),X39)|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40))&(r2_hidden(esk9_2(X39,X40),X39)|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40)))&((~r2_hidden(k4_tarski(esk8_2(X39,X40),esk9_2(X39,X40)),X40)|~r1_tarski(esk8_2(X39,X40),esk9_2(X39,X40))|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40))&(r2_hidden(k4_tarski(esk8_2(X39,X40),esk9_2(X39,X40)),X40)|r1_tarski(esk8_2(X39,X40),esk9_2(X39,X40))|k3_relat_1(X40)!=X39|X40=k1_wellord2(X39)|~v1_relat_1(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.12/0.39  fof(c_0_13, plain, ![X45]:v1_relat_1(k1_wellord2(X45)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.39  fof(c_0_14, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(esk5_3(X24,X25,X26),X26),X24)|X25!=k2_relat_1(X24))&(~r2_hidden(k4_tarski(X29,X28),X24)|r2_hidden(X28,X25)|X25!=k2_relat_1(X24)))&((~r2_hidden(esk6_2(X30,X31),X31)|~r2_hidden(k4_tarski(X33,esk6_2(X30,X31)),X30)|X31=k2_relat_1(X30))&(r2_hidden(esk6_2(X30,X31),X31)|r2_hidden(k4_tarski(esk7_2(X30,X31),esk6_2(X30,X31)),X30)|X31=k2_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.39  cnf(c_0_15, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_11])).
% 0.12/0.39  fof(c_0_17, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.39  cnf(c_0_18, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_20, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_22, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.39  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_24, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20])])).
% 0.12/0.39  fof(c_0_27, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.39  cnf(c_0_28, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_21])).
% 0.12/0.39  cnf(c_0_30, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  fof(c_0_32, plain, ![X35]:(~v1_relat_1(X35)|r1_tarski(X35,k2_zfmisc_1(k1_relat_1(X35),k2_relat_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.12/0.39  cnf(c_0_33, plain, (r2_hidden(esk1_2(k1_relat_1(X1),X2),k3_relat_1(X1))|r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.12/0.39  cnf(c_0_34, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_20])])).
% 0.12/0.39  cnf(c_0_35, plain, (r2_hidden(X1,k1_relat_1(k1_wellord2(X2)))|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.39  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.39  cnf(c_0_37, plain, (r2_hidden(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.39  cnf(c_0_38, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_30])).
% 0.12/0.39  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_31, c_0_23])).
% 0.12/0.39  cnf(c_0_40, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.39  cnf(c_0_41, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_42, plain, (r2_hidden(esk1_2(k1_relat_1(k1_wellord2(X1)),X2),X1)|r1_tarski(k1_relat_1(k1_wellord2(X1)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_20]), c_0_34])).
% 0.12/0.39  cnf(c_0_43, plain, (r2_hidden(X1,k1_relat_1(k1_wellord2(X2)))|r1_tarski(X2,X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,esk1_2(X2,X3))), inference(spm,[status(thm)],[c_0_35, c_0_23])).
% 0.12/0.39  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 0.12/0.39  cnf(c_0_45, plain, (r2_hidden(esk1_2(k2_relat_1(X1),X2),k3_relat_1(X1))|r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_23])).
% 0.12/0.39  cnf(c_0_46, plain, (r2_hidden(X1,k2_relat_1(k1_wellord2(X2)))|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_38, c_0_26])).
% 0.12/0.39  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.12/0.39  cnf(c_0_48, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.39  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(k1_wellord2(X1)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.39  cnf(c_0_50, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(k1_wellord2(X1)))|r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_23])).
% 0.12/0.39  cnf(c_0_51, plain, (r2_hidden(esk1_2(k2_relat_1(k1_wellord2(X1)),X2),X1)|r1_tarski(k2_relat_1(k1_wellord2(X1)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_20]), c_0_34])).
% 0.12/0.39  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),k2_relat_1(k1_wellord2(X1)))|r1_tarski(X1,X2)|~r2_hidden(X3,X1)|~r1_tarski(X3,esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_23])).
% 0.12/0.39  cnf(c_0_53, plain, (r2_hidden(esk1_2(k1_wellord2(X1),X2),k2_zfmisc_1(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))))|r1_tarski(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_47, c_0_20])).
% 0.12/0.39  cnf(c_0_54, plain, (k1_relat_1(k1_wellord2(X1))=X1|~r1_tarski(X1,k1_relat_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.39  cnf(c_0_55, plain, (r1_tarski(X1,k1_relat_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_50])).
% 0.12/0.39  cnf(c_0_56, plain, (r1_tarski(k2_relat_1(k1_wellord2(X1)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_51])).
% 0.12/0.39  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),k2_relat_1(k1_wellord2(X1)))|r1_tarski(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_44]), c_0_23])).
% 0.12/0.39  fof(c_0_58, negated_conjecture, ~(![X1]:r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(assume_negation,[status(cth)],[t33_wellord2])).
% 0.12/0.39  cnf(c_0_59, plain, (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(k1_relat_1(k1_wellord2(X1)),k2_relat_1(k1_wellord2(X1))))), inference(spm,[status(thm)],[c_0_41, c_0_53])).
% 0.12/0.39  cnf(c_0_60, plain, (k1_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.12/0.39  cnf(c_0_61, plain, (k2_relat_1(k1_wellord2(X1))=X1|~r1_tarski(X1,k2_relat_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_48, c_0_56])).
% 0.12/0.39  cnf(c_0_62, plain, (r1_tarski(X1,k2_relat_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_57])).
% 0.12/0.39  fof(c_0_63, negated_conjecture, ~r1_tarski(k1_wellord2(esk10_0),k2_zfmisc_1(esk10_0,esk10_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_58])])])).
% 0.12/0.39  cnf(c_0_64, plain, (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,k2_relat_1(k1_wellord2(X1))))), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.12/0.39  cnf(c_0_65, plain, (k2_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.12/0.39  cnf(c_0_66, negated_conjecture, (~r1_tarski(k1_wellord2(esk10_0),k2_zfmisc_1(esk10_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.12/0.39  cnf(c_0_67, plain, (r1_tarski(k1_wellord2(X1),k2_zfmisc_1(X1,X1))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 69
% 0.12/0.39  # Proof object clause steps            : 50
% 0.12/0.39  # Proof object formula steps           : 19
% 0.12/0.39  # Proof object conjectures             : 5
% 0.12/0.39  # Proof object clause conjectures      : 2
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 16
% 0.12/0.39  # Proof object initial formulas used   : 9
% 0.12/0.39  # Proof object generating inferences   : 22
% 0.12/0.39  # Proof object simplifying inferences  : 23
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 9
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 26
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 26
% 0.12/0.39  # Processed clauses                    : 232
% 0.12/0.39  # ...of these trivial                  : 1
% 0.12/0.39  # ...subsumed                          : 44
% 0.12/0.39  # ...remaining for further processing  : 187
% 0.12/0.39  # Other redundant clauses eliminated   : 13
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 2
% 0.12/0.39  # Backward-rewritten                   : 64
% 0.12/0.39  # Generated clauses                    : 891
% 0.12/0.39  # ...of the previous two non-trivial   : 906
% 0.12/0.39  # Contextual simplify-reflections      : 4
% 0.12/0.39  # Paramodulations                      : 876
% 0.12/0.39  # Factorizations                       : 2
% 0.12/0.39  # Equation resolutions                 : 13
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 83
% 0.12/0.39  #    Positive orientable unit clauses  : 6
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 0
% 0.12/0.39  #    Non-unit-clauses                  : 77
% 0.12/0.39  # Current number of unprocessed clauses: 713
% 0.12/0.39  # ...number of literals in the above   : 2446
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 91
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 4288
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 2247
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 50
% 0.12/0.39  # Unit Clause-clause subsumption calls : 90
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 14
% 0.12/0.39  # BW rewrite match successes           : 10
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 19953
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.051 s
% 0.12/0.39  # System time              : 0.007 s
% 0.12/0.39  # Total time               : 0.058 s
% 0.12/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
