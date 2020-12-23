%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 216 expanded)
%              Number of clauses        :   27 (  81 expanded)
%              Number of leaves         :    4 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 (1301 expanded)
%              Number of equality atoms :   38 ( 389 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

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

fof(t9_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_4,plain,(
    ! [X13,X14,X15] :
      ( ( r2_hidden(X13,k1_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(X14,k2_relat_1(X15))
        | ~ r2_hidden(k4_tarski(X13,X14),X15)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

fof(c_0_5,plain,(
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

cnf(c_0_6,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X1 = X2
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( k1_relat_1(X1) = k1_relat_1(X2)
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_1])).

fof(c_0_9,plain,(
    ! [X16,X17,X18] :
      ( ( r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X17 = k1_funct_1(X18,X16)
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X16,k1_relat_1(X18))
        | X17 != k1_funct_1(X18,X16)
        | r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_10,plain,
    ( X1 = X2
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

fof(c_0_11,negated_conjecture,(
    ! [X21] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & k1_relat_1(esk3_0) = k1_relat_1(esk4_0)
      & ( ~ r2_hidden(X21,k1_relat_1(esk3_0))
        | k1_funct_1(esk3_0,X21) = k1_funct_1(esk4_0,X21) )
      & esk3_0 != esk4_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_12,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_6,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X1 = X2
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = X1
    | r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(esk4_0))
    | r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | esk2_2(X1,X2) = k1_funct_1(X1,esk1_2(X1,X2))
    | X1 = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,esk4_0),k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X1,esk1_2(X1,X2))
    | X1 = X2
    | k1_funct_1(X2,esk1_2(X1,X2)) != k1_funct_1(X1,esk1_2(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(ef,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk3_0,esk1_2(esk3_0,esk4_0)) = k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk3_0,X1)),esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_14]),c_0_26]),c_0_15])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_32,negated_conjecture,
    ( esk2_2(esk3_0,esk4_0) = k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_26]),c_0_29]),c_0_15]),c_0_19])]),c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_29]),c_0_19])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_19]),c_0_15])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:39:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.19/0.38  # and selection function SelectNewComplexAHP.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.026 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.19/0.38  fof(d2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X1=X2<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)<=>r2_hidden(k4_tarski(X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_relat_1)).
% 0.19/0.38  fof(t9_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.38  fof(c_0_4, plain, ![X13, X14, X15]:((r2_hidden(X13,k1_relat_1(X15))|~r2_hidden(k4_tarski(X13,X14),X15)|~v1_relat_1(X15))&(r2_hidden(X14,k2_relat_1(X15))|~r2_hidden(k4_tarski(X13,X14),X15)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.19/0.38  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(k4_tarski(X7,X8),X5)|r2_hidden(k4_tarski(X7,X8),X6)|X5!=X6|~v1_relat_1(X6)|~v1_relat_1(X5))&(~r2_hidden(k4_tarski(X9,X10),X6)|r2_hidden(k4_tarski(X9,X10),X5)|X5!=X6|~v1_relat_1(X6)|~v1_relat_1(X5)))&((~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)|~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X5=X6|~v1_relat_1(X6)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X5)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X5=X6|~v1_relat_1(X6)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_relat_1])])])])])])).
% 0.19/0.38  cnf(c_0_6, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.38  cnf(c_0_7, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|X1=X2|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2)))), inference(assume_negation,[status(cth)],[t9_funct_1])).
% 0.19/0.38  fof(c_0_9, plain, ![X16, X17, X18]:(((r2_hidden(X16,k1_relat_1(X18))|~r2_hidden(k4_tarski(X16,X17),X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(X17=k1_funct_1(X18,X16)|~r2_hidden(k4_tarski(X16,X17),X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(~r2_hidden(X16,k1_relat_1(X18))|X17!=k1_funct_1(X18,X16)|r2_hidden(k4_tarski(X16,X17),X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.38  cnf(c_0_10, plain, (X1=X2|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_6, c_0_7])).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ![X21]:((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((k1_relat_1(esk3_0)=k1_relat_1(esk4_0)&(~r2_hidden(X21,k1_relat_1(esk3_0))|k1_funct_1(esk3_0,X21)=k1_funct_1(esk4_0,X21)))&esk3_0!=esk4_0))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 0.19/0.38  cnf(c_0_12, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_13, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))|r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_6, c_0_10])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (k1_relat_1(esk3_0)=k1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_16, plain, (esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|X1=X2|r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_7])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (k1_funct_1(esk3_0,X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (esk3_0=X1|r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(esk4_0))|r2_hidden(esk1_2(esk3_0,X1),k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_22, plain, (esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|esk2_2(X1,X2)=k1_funct_1(X1,esk1_2(X1,X2))|X1=X2|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_12, c_0_16])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (k1_funct_1(esk3_0,X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_17, c_0_14])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk1_2(esk3_0,esk4_0),k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_27, plain, (esk2_2(X1,X2)=k1_funct_1(X1,esk1_2(X1,X2))|X1=X2|k1_funct_1(X2,esk1_2(X1,X2))!=k1_funct_1(X1,esk1_2(X1,X2))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(ef,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk3_0,esk1_2(esk3_0,esk4_0))=k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk3_0,X1)),esk3_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_14]), c_0_26]), c_0_15])])).
% 0.19/0.38  cnf(c_0_31, plain, (X1=X2|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (esk2_2(esk3_0,esk4_0)=k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_26]), c_0_29]), c_0_15]), c_0_19])]), c_0_20])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_29]), c_0_19])])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0))),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_28])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_19]), c_0_15])]), c_0_20]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 36
% 0.19/0.38  # Proof object clause steps            : 27
% 0.19/0.38  # Proof object formula steps           : 9
% 0.19/0.38  # Proof object conjectures             : 19
% 0.19/0.38  # Proof object clause conjectures      : 16
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 12
% 0.19/0.38  # Proof object initial formulas used   : 4
% 0.19/0.38  # Proof object generating inferences   : 14
% 0.19/0.38  # Proof object simplifying inferences  : 25
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 4
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 16
% 0.19/0.38  # Removed in clause preprocessing      : 2
% 0.19/0.38  # Initial clauses in saturation        : 14
% 0.19/0.38  # Processed clauses                    : 158
% 0.19/0.38  # ...of these trivial                  : 4
% 0.19/0.38  # ...subsumed                          : 47
% 0.19/0.38  # ...remaining for further processing  : 107
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 290
% 0.19/0.38  # ...of the previous two non-trivial   : 222
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 269
% 0.19/0.38  # Factorizations                       : 16
% 0.19/0.38  # Equation resolutions                 : 5
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 107
% 0.19/0.38  #    Positive orientable unit clauses  : 18
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 88
% 0.19/0.38  # Current number of unprocessed clauses: 78
% 0.19/0.38  # ...number of literals in the above   : 538
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 0
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 827
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 121
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 49
% 0.19/0.38  # Unit Clause-clause subsumption calls : 27
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 6
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 10637
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.036 s
% 0.19/0.38  # System time              : 0.007 s
% 0.19/0.38  # Total time               : 0.043 s
% 0.19/0.38  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
