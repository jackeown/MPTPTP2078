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
% DateTime   : Thu Dec  3 10:53:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 128 expanded)
%              Number of clauses        :   29 (  47 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  200 ( 768 expanded)
%              Number of equality atoms :   58 ( 275 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(t44_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = X1 )
           => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(c_0_5,plain,(
    ! [X18,X19,X20,X21,X22,X24,X25,X26,X29] :
      ( ( r2_hidden(k4_tarski(X21,esk4_5(X18,X19,X20,X21,X22)),X18)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk4_5(X18,X19,X20,X21,X22),X22),X19)
        | ~ r2_hidden(k4_tarski(X21,X22),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X24,X26),X18)
        | ~ r2_hidden(k4_tarski(X26,X25),X19)
        | r2_hidden(k4_tarski(X24,X25),X20)
        | X20 != k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | ~ r2_hidden(k4_tarski(esk5_3(X18,X19,X20),X29),X18)
        | ~ r2_hidden(k4_tarski(X29,esk6_3(X18,X19,X20)),X19)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk7_3(X18,X19,X20)),X18)
        | r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk7_3(X18,X19,X20),esk6_3(X18,X19,X20)),X19)
        | r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)
        | X20 = k5_relat_1(X18,X19)
        | ~ v1_relat_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( k2_relat_1(X1) = k1_relat_1(X2)
                & k5_relat_1(X1,X2) = X1 )
             => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_funct_1])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & k2_relat_1(esk9_0) = k1_relat_1(esk10_0)
    & k5_relat_1(esk9_0,esk10_0) = esk9_0
    & esk10_0 != k6_relat_1(k1_relat_1(esk10_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_10,plain,(
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

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k5_relat_1(esk9_0,esk10_0) = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,esk4_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ v1_relat_1(k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X11,X12,X13,X14,X16] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X9),X7)
        | X8 != k2_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X12,X11),X7)
        | r2_hidden(X11,X8)
        | X8 != k2_relat_1(X7) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | ~ r2_hidden(k4_tarski(X16,esk2_2(X13,X14)),X13)
        | X14 = k2_relat_1(X13) )
      & ( r2_hidden(esk2_2(X13,X14),X14)
        | r2_hidden(k4_tarski(esk3_2(X13,X14),esk2_2(X13,X14)),X13)
        | X14 = k2_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_5(esk9_0,esk10_0,esk9_0,X1,X2),X2),esk10_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_5(esk9_0,esk10_0,esk9_0,X1,X2)),esk9_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk10_0,esk4_5(esk9_0,esk10_0,esk9_0,X1,X2)) = X2
    | ~ r2_hidden(k4_tarski(X1,X2),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_14])])).

cnf(c_0_24,negated_conjecture,
    ( esk4_5(esk9_0,esk10_0,esk9_0,X1,X2) = k1_funct_1(esk9_0,X1)
    | ~ r2_hidden(k4_tarski(X1,X2),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_20]),c_0_21]),c_0_13])])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( k2_relat_1(esk9_0) = k1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1)) = X2
    | ~ r2_hidden(k4_tarski(X1,X2),esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk9_0,k1_relat_1(esk10_0),X1),X1),esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X31,X32,X33] :
      ( ( k1_relat_1(X32) = X31
        | X32 != k6_relat_1(X31)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X33,X31)
        | k1_funct_1(X32,X33) = X33
        | X32 != k6_relat_1(X31)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( r2_hidden(esk8_2(X31,X32),X31)
        | k1_relat_1(X32) != X31
        | X32 = k6_relat_1(X31)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( k1_funct_1(X32,esk8_2(X31,X32)) != esk8_2(X31,X32)
        | k1_relat_1(X32) != X31
        | X32 = k6_relat_1(X31)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk1_3(esk9_0,k1_relat_1(esk10_0),X1))) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_3(esk9_0,k1_relat_1(esk10_0),X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_28]),c_0_21]),c_0_13])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk8_2(X2,X1)) != esk8_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk10_0,X1) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk8_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk10_0 != k6_relat_1(k1_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk8_2(k1_relat_1(X1),X1)) != esk8_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0)) = esk8_2(k1_relat_1(esk10_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19]),c_0_14])]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_19]),c_0_14])]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:04:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.029 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 0.19/0.39  fof(t44_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 0.19/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.39  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.19/0.39  fof(c_0_5, plain, ![X18, X19, X20, X21, X22, X24, X25, X26, X29]:((((r2_hidden(k4_tarski(X21,esk4_5(X18,X19,X20,X21,X22)),X18)|~r2_hidden(k4_tarski(X21,X22),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk4_5(X18,X19,X20,X21,X22),X22),X19)|~r2_hidden(k4_tarski(X21,X22),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18)))&(~r2_hidden(k4_tarski(X24,X26),X18)|~r2_hidden(k4_tarski(X26,X25),X19)|r2_hidden(k4_tarski(X24,X25),X20)|X20!=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18)))&((~r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)|(~r2_hidden(k4_tarski(esk5_3(X18,X19,X20),X29),X18)|~r2_hidden(k4_tarski(X29,esk6_3(X18,X19,X20)),X19))|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&((r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk7_3(X18,X19,X20)),X18)|r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk7_3(X18,X19,X20),esk6_3(X18,X19,X20)),X19)|r2_hidden(k4_tarski(esk5_3(X18,X19,X20),esk6_3(X18,X19,X20)),X20)|X20=k5_relat_1(X18,X19)|~v1_relat_1(X20)|~v1_relat_1(X19)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.19/0.39  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t44_funct_1])).
% 0.19/0.39  cnf(c_0_7, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk9_0)&v1_funct_1(esk9_0))&((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&((k2_relat_1(esk9_0)=k1_relat_1(esk10_0)&k5_relat_1(esk9_0,esk10_0)=esk9_0)&esk10_0!=k6_relat_1(k1_relat_1(esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.39  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,esk4_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.39  fof(c_0_10, plain, ![X35, X36, X37]:(((r2_hidden(X35,k1_relat_1(X37))|~r2_hidden(k4_tarski(X35,X36),X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(X36=k1_funct_1(X37,X35)|~r2_hidden(k4_tarski(X35,X36),X37)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(~r2_hidden(X35,k1_relat_1(X37))|X36!=k1_funct_1(X37,X35)|r2_hidden(k4_tarski(X35,X36),X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.39  cnf(c_0_11, plain, (r2_hidden(k4_tarski(esk4_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_7])).
% 0.19/0.39  cnf(c_0_12, negated_conjecture, (k5_relat_1(esk9_0,esk10_0)=esk9_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,esk4_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~v1_relat_1(k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))), inference(er,[status(thm)],[c_0_9])).
% 0.19/0.39  fof(c_0_16, plain, ![X7, X8, X9, X11, X12, X13, X14, X16]:(((~r2_hidden(X9,X8)|r2_hidden(k4_tarski(esk1_3(X7,X8,X9),X9),X7)|X8!=k2_relat_1(X7))&(~r2_hidden(k4_tarski(X12,X11),X7)|r2_hidden(X11,X8)|X8!=k2_relat_1(X7)))&((~r2_hidden(esk2_2(X13,X14),X14)|~r2_hidden(k4_tarski(X16,esk2_2(X13,X14)),X13)|X14=k2_relat_1(X13))&(r2_hidden(esk2_2(X13,X14),X14)|r2_hidden(k4_tarski(esk3_2(X13,X14),esk2_2(X13,X14)),X13)|X14=k2_relat_1(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.39  cnf(c_0_17, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (r2_hidden(k4_tarski(esk4_5(esk9_0,esk10_0,esk9_0,X1,X2),X2),esk10_0)|~r2_hidden(k4_tarski(X1,X2),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_5(esk9_0,esk10_0,esk9_0,X1,X2)),esk9_0)|~r2_hidden(k4_tarski(X1,X2),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_12]), c_0_13]), c_0_14])])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (k1_funct_1(esk10_0,esk4_5(esk9_0,esk10_0,esk9_0,X1,X2))=X2|~r2_hidden(k4_tarski(X1,X2),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_14])])).
% 0.19/0.39  cnf(c_0_24, negated_conjecture, (esk4_5(esk9_0,esk10_0,esk9_0,X1,X2)=k1_funct_1(esk9_0,X1)|~r2_hidden(k4_tarski(X1,X2),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_20]), c_0_21]), c_0_13])])).
% 0.19/0.39  cnf(c_0_25, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (k2_relat_1(esk9_0)=k1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk10_0,k1_funct_1(esk9_0,X1))=X2|~r2_hidden(k4_tarski(X1,X2),esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk9_0,k1_relat_1(esk10_0),X1),X1),esk9_0)|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  fof(c_0_29, plain, ![X31, X32, X33]:(((k1_relat_1(X32)=X31|X32!=k6_relat_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(~r2_hidden(X33,X31)|k1_funct_1(X32,X33)=X33|X32!=k6_relat_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&((r2_hidden(esk8_2(X31,X32),X31)|k1_relat_1(X32)!=X31|X32=k6_relat_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(k1_funct_1(X32,esk8_2(X31,X32))!=esk8_2(X31,X32)|k1_relat_1(X32)!=X31|X32=k6_relat_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.19/0.39  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk10_0,k1_funct_1(esk9_0,esk1_3(esk9_0,k1_relat_1(esk10_0),X1)))=X1|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_26]), c_0_26])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk9_0,esk1_3(esk9_0,k1_relat_1(esk10_0),X1))=X1|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_28]), c_0_21]), c_0_13])])).
% 0.19/0.39  cnf(c_0_32, plain, (r2_hidden(esk8_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_33, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk8_2(X2,X1))!=esk8_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk10_0,X1)=X1|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.39  cnf(c_0_35, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk8_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (esk10_0!=k6_relat_1(k1_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_37, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk8_2(k1_relat_1(X1),X1))!=esk8_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk10_0,esk8_2(k1_relat_1(esk10_0),esk10_0))=esk8_2(k1_relat_1(esk10_0),esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19]), c_0_14])]), c_0_36])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_19]), c_0_14])]), c_0_36]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 40
% 0.19/0.39  # Proof object clause steps            : 29
% 0.19/0.39  # Proof object formula steps           : 11
% 0.19/0.39  # Proof object conjectures             : 21
% 0.19/0.39  # Proof object clause conjectures      : 18
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 13
% 0.19/0.39  # Proof object initial formulas used   : 5
% 0.19/0.39  # Proof object generating inferences   : 11
% 0.19/0.39  # Proof object simplifying inferences  : 30
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 5
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 24
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 24
% 0.19/0.39  # Processed clauses                    : 150
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 21
% 0.19/0.39  # ...remaining for further processing  : 129
% 0.19/0.39  # Other redundant clauses eliminated   : 10
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 0
% 0.19/0.39  # Generated clauses                    : 423
% 0.19/0.39  # ...of the previous two non-trivial   : 410
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 407
% 0.19/0.39  # Factorizations                       : 6
% 0.19/0.39  # Equation resolutions                 : 10
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 95
% 0.19/0.39  #    Positive orientable unit clauses  : 7
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 1
% 0.19/0.39  #    Non-unit-clauses                  : 87
% 0.19/0.39  # Current number of unprocessed clauses: 308
% 0.19/0.39  # ...number of literals in the above   : 1656
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 24
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1044
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 548
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 21
% 0.19/0.39  # Unit Clause-clause subsumption calls : 11
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 0
% 0.19/0.39  # BW rewrite match successes           : 0
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 13670
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.046 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.050 s
% 0.19/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
