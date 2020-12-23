%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:36 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 788 expanded)
%              Number of clauses        :   38 ( 299 expanded)
%              Number of leaves         :    9 ( 193 expanded)
%              Depth                    :   15
%              Number of atoms          :  186 (3488 expanded)
%              Number of equality atoms :   53 (1261 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t166_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( k1_relat_1(X1) = k1_relat_1(X2)
                & ! [X4] :
                    ( r2_hidden(X4,X3)
                   => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) )
             => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t189_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(t89_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t165_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(X3,k1_relat_1(X2)) )
             => ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
              <=> ! [X4] :
                    ( r2_hidden(X4,X3)
                   => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

fof(t86_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X1,k1_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( k1_relat_1(X1) = k1_relat_1(X2)
                  & ! [X4] :
                      ( r2_hidden(X4,X3)
                     => k1_funct_1(X1,X4) = k1_funct_1(X2,X4) ) )
               => k7_relat_1(X1,X3) = k7_relat_1(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t166_funct_1])).

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | ~ r1_tarski(X15,k1_relat_1(X16))
      | k1_relat_1(k7_relat_1(X16,X15)) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_11,negated_conjecture,(
    ! [X26] :
      ( v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & k1_relat_1(esk2_0) = k1_relat_1(esk3_0)
      & ( ~ r2_hidden(X26,esk4_0)
        | k1_funct_1(esk2_0,X26) = k1_funct_1(esk3_0,X26) )
      & k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k1_relat_1(esk2_0) = k1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | r1_tarski(k1_relat_1(k7_relat_1(X12,X11)),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k7_relat_1(X5,k1_relat_1(X6)) = k7_relat_1(X5,k1_relat_1(k7_relat_1(X6,k1_relat_1(X5)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).

cnf(c_0_17,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | r1_tarski(k1_relat_1(k7_relat_1(X14,X13)),k1_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))) = k7_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_14])])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_26,plain,(
    ! [X7] :
      ( k1_relat_1(k6_relat_1(X7)) = X7
      & k2_relat_1(k6_relat_1(X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_27,plain,(
    ! [X17] :
      ( v1_relat_1(k6_relat_1(X17))
      & v1_funct_1(k6_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_13]),c_0_14])])).

cnf(c_0_29,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1)))) = k7_relat_1(esk2_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_24]),c_0_25])])).

cnf(c_0_30,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,X1)))) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_28]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,X1))) = k7_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_34,plain,(
    ! [X18,X19,X20,X21] :
      ( ( k7_relat_1(X18,X20) != k7_relat_1(X19,X20)
        | ~ r2_hidden(X21,X20)
        | k1_funct_1(X18,X21) = k1_funct_1(X19,X21)
        | ~ r1_tarski(X20,k1_relat_1(X18))
        | ~ r1_tarski(X20,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk1_3(X18,X19,X20),X20)
        | k7_relat_1(X18,X20) = k7_relat_1(X19,X20)
        | ~ r1_tarski(X20,k1_relat_1(X18))
        | ~ r1_tarski(X20,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( k1_funct_1(X18,esk1_3(X18,X19,X20)) != k1_funct_1(X19,esk1_3(X18,X19,X20))
        | k7_relat_1(X18,X20) = k7_relat_1(X19,X20)
        | ~ r1_tarski(X20,k1_relat_1(X18))
        | ~ r1_tarski(X20,k1_relat_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(X1))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(esk3_0,X2))) = k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,X2)))
    | r2_hidden(esk1_3(X1,esk2_0,k1_relat_1(k7_relat_1(esk3_0,X2))),k1_relat_1(k7_relat_1(esk3_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_37]),c_0_25])])).

cnf(c_0_40,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk2_0,X1)))) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23]),c_0_25])])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(X1)))) = k7_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_38])).

cnf(c_0_42,plain,
    ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | k1_funct_1(X1,esk1_3(X1,X2,X3)) != k1_funct_1(X2,esk1_3(X1,X2,X3))
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk2_0,X1) = k1_funct_1(esk3_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_45,plain,(
    ! [X8,X9,X10] :
      ( ( r2_hidden(X8,X9)
        | ~ r2_hidden(X8,k1_relat_1(k7_relat_1(X10,X9)))
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(X8,k1_relat_1(X10))
        | ~ r2_hidden(X8,k1_relat_1(k7_relat_1(X10,X9)))
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(X8,X9)
        | ~ r2_hidden(X8,k1_relat_1(X10))
        | r2_hidden(X8,k1_relat_1(k7_relat_1(X10,X9)))
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_46,negated_conjecture,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(esk2_0,X2))) = k7_relat_1(esk2_0,X2)
    | r2_hidden(esk1_3(X1,esk2_0,k1_relat_1(k7_relat_1(esk2_0,X2))),k1_relat_1(k7_relat_1(esk2_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_33]),c_0_35]),c_0_35]),c_0_35]),c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_40]),c_0_13]),c_0_14])])).

cnf(c_0_48,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk2_0,X1))) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_31])])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(X2,X1)
    | k1_funct_1(esk2_0,esk1_3(esk3_0,X2,X1)) != k1_funct_1(X2,esk1_3(esk3_0,X2,X1))
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k1_relat_1(X2))
    | ~ r2_hidden(esk1_3(esk3_0,X2,X1),esk4_0)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_13]),c_0_14])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(esk2_0,X1)
    | r2_hidden(esk1_3(esk3_0,esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1))),k1_relat_1(k7_relat_1(esk2_0,X1))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_13]),c_0_44]),c_0_47]),c_0_14])]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(esk2_0,X1)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r2_hidden(esk1_3(esk3_0,esk2_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_49]),c_0_37]),c_0_25])])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(esk2_0,X1)
    | r2_hidden(esk1_3(esk3_0,esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_25])])).

cnf(c_0_54,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1))) = k7_relat_1(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(esk2_0,esk4_0) != k7_relat_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_48]),c_0_54]),c_0_47])]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:39:11 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.32  # No SInE strategy applied
% 0.12/0.32  # Trying AutoSched0 for 299 seconds
% 2.30/2.53  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.30/2.53  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.30/2.53  #
% 2.30/2.53  # Preprocessing time       : 0.021 s
% 2.30/2.53  # Presaturation interreduction done
% 2.30/2.53  
% 2.30/2.53  # Proof found!
% 2.30/2.53  # SZS status Theorem
% 2.30/2.53  # SZS output start CNFRefutation
% 2.30/2.53  fof(t166_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 2.30/2.53  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.30/2.53  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.30/2.53  fof(t189_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.30/2.53  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.30/2.53  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.30/2.53  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.30/2.53  fof(t165_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 2.30/2.53  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.30/2.53  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t166_funct_1])).
% 2.30/2.53  fof(c_0_10, plain, ![X15, X16]:(~v1_relat_1(X16)|(~r1_tarski(X15,k1_relat_1(X16))|k1_relat_1(k7_relat_1(X16,X15))=X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 2.30/2.53  fof(c_0_11, negated_conjecture, ![X26]:((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((k1_relat_1(esk2_0)=k1_relat_1(esk3_0)&(~r2_hidden(X26,esk4_0)|k1_funct_1(esk2_0,X26)=k1_funct_1(esk3_0,X26)))&k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 2.30/2.53  cnf(c_0_12, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.30/2.53  cnf(c_0_13, negated_conjecture, (k1_relat_1(esk2_0)=k1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.30/2.53  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.30/2.53  fof(c_0_15, plain, ![X11, X12]:(~v1_relat_1(X12)|r1_tarski(k1_relat_1(k7_relat_1(X12,X11)),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 2.30/2.53  fof(c_0_16, plain, ![X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|k7_relat_1(X5,k1_relat_1(X6))=k7_relat_1(X5,k1_relat_1(k7_relat_1(X6,k1_relat_1(X5)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).
% 2.30/2.53  cnf(c_0_17, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 2.30/2.53  cnf(c_0_18, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.30/2.53  cnf(c_0_19, plain, (k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.30/2.53  fof(c_0_20, plain, ![X13, X14]:(~v1_relat_1(X14)|r1_tarski(k1_relat_1(k7_relat_1(X14,X13)),k1_relat_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 2.30/2.53  cnf(c_0_21, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))))=k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 2.30/2.53  cnf(c_0_22, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0))))=k7_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_14])])).
% 2.30/2.53  cnf(c_0_23, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.30/2.53  cnf(c_0_24, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1)))=k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 2.30/2.53  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.30/2.53  fof(c_0_26, plain, ![X7]:(k1_relat_1(k6_relat_1(X7))=X7&k2_relat_1(k6_relat_1(X7))=X7), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 2.30/2.53  fof(c_0_27, plain, ![X17]:(v1_relat_1(k6_relat_1(X17))&v1_funct_1(k6_relat_1(X17))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 2.30/2.53  cnf(c_0_28, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_13]), c_0_14])])).
% 2.30/2.53  cnf(c_0_29, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1))))=k7_relat_1(esk2_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_24]), c_0_25])])).
% 2.30/2.53  cnf(c_0_30, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.30/2.53  cnf(c_0_31, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 2.30/2.53  cnf(c_0_32, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,X1))))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_28]), c_0_25])])).
% 2.30/2.53  cnf(c_0_33, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,X1)))=k7_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 2.30/2.53  fof(c_0_34, plain, ![X18, X19, X20, X21]:((k7_relat_1(X18,X20)!=k7_relat_1(X19,X20)|(~r2_hidden(X21,X20)|k1_funct_1(X18,X21)=k1_funct_1(X19,X21))|(~r1_tarski(X20,k1_relat_1(X18))|~r1_tarski(X20,k1_relat_1(X19)))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&((r2_hidden(esk1_3(X18,X19,X20),X20)|k7_relat_1(X18,X20)=k7_relat_1(X19,X20)|(~r1_tarski(X20,k1_relat_1(X18))|~r1_tarski(X20,k1_relat_1(X19)))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(k1_funct_1(X18,esk1_3(X18,X19,X20))!=k1_funct_1(X19,esk1_3(X18,X19,X20))|k7_relat_1(X18,X20)=k7_relat_1(X19,X20)|(~r1_tarski(X20,k1_relat_1(X18))|~r1_tarski(X20,k1_relat_1(X19)))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).
% 2.30/2.53  cnf(c_0_35, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 2.30/2.53  cnf(c_0_36, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.30/2.53  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.30/2.53  cnf(c_0_38, negated_conjecture, (k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(X1)))=k1_relat_1(k7_relat_1(X1,k1_relat_1(esk2_0)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_24, c_0_35])).
% 2.30/2.53  cnf(c_0_39, negated_conjecture, (k7_relat_1(X1,k1_relat_1(k7_relat_1(esk3_0,X2)))=k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk3_0,X2)))|r2_hidden(esk1_3(X1,esk2_0,k1_relat_1(k7_relat_1(esk3_0,X2))),k1_relat_1(k7_relat_1(esk3_0,X2)))|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_37]), c_0_25])])).
% 2.30/2.53  cnf(c_0_40, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk2_0,X1))))=k1_relat_1(k7_relat_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_23]), c_0_25])])).
% 2.30/2.53  cnf(c_0_41, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk2_0,k1_relat_1(X1))))=k7_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_38])).
% 2.30/2.53  cnf(c_0_42, plain, (k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|k1_funct_1(X1,esk1_3(X1,X2,X3))!=k1_funct_1(X2,esk1_3(X1,X2,X3))|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.30/2.53  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk2_0,X1)=k1_funct_1(esk3_0,X1)|~r2_hidden(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.30/2.53  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.30/2.53  fof(c_0_45, plain, ![X8, X9, X10]:(((r2_hidden(X8,X9)|~r2_hidden(X8,k1_relat_1(k7_relat_1(X10,X9)))|~v1_relat_1(X10))&(r2_hidden(X8,k1_relat_1(X10))|~r2_hidden(X8,k1_relat_1(k7_relat_1(X10,X9)))|~v1_relat_1(X10)))&(~r2_hidden(X8,X9)|~r2_hidden(X8,k1_relat_1(X10))|r2_hidden(X8,k1_relat_1(k7_relat_1(X10,X9)))|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 2.30/2.53  cnf(c_0_46, negated_conjecture, (k7_relat_1(X1,k1_relat_1(k7_relat_1(esk2_0,X2)))=k7_relat_1(esk2_0,X2)|r2_hidden(esk1_3(X1,esk2_0,k1_relat_1(k7_relat_1(esk2_0,X2))),k1_relat_1(k7_relat_1(esk2_0,X2)))|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_33]), c_0_35]), c_0_35]), c_0_35]), c_0_35])).
% 2.30/2.53  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk2_0,X1)),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_40]), c_0_13]), c_0_14])])).
% 2.30/2.53  cnf(c_0_48, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk2_0,X1)))=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_31])])).
% 2.30/2.53  cnf(c_0_49, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(X2,X1)|k1_funct_1(esk2_0,esk1_3(esk3_0,X2,X1))!=k1_funct_1(X2,esk1_3(esk3_0,X2,X1))|~v1_funct_1(X2)|~r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(X1,k1_relat_1(X2))|~r2_hidden(esk1_3(esk3_0,X2,X1),esk4_0)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_13]), c_0_14])])).
% 2.30/2.53  cnf(c_0_50, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.30/2.53  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(esk2_0,X1)|r2_hidden(esk1_3(esk3_0,esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1))),k1_relat_1(k7_relat_1(esk2_0,X1)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_13]), c_0_44]), c_0_47]), c_0_14])]), c_0_48])).
% 2.30/2.53  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(esk2_0,X1)|~r1_tarski(X1,k1_relat_1(esk2_0))|~r2_hidden(esk1_3(esk3_0,esk2_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_49]), c_0_37]), c_0_25])])).
% 2.30/2.53  cnf(c_0_53, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(esk2_0,X1)|r2_hidden(esk1_3(esk3_0,esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_25])])).
% 2.30/2.53  cnf(c_0_54, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(k7_relat_1(esk2_0,X1)))=k7_relat_1(esk2_0,X1)), inference(rw,[status(thm)],[c_0_33, c_0_35])).
% 2.30/2.53  cnf(c_0_55, negated_conjecture, (k7_relat_1(esk2_0,esk4_0)!=k7_relat_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.30/2.53  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_48]), c_0_54]), c_0_47])]), c_0_55]), ['proof']).
% 2.30/2.53  # SZS output end CNFRefutation
% 2.30/2.53  # Proof object total steps             : 57
% 2.30/2.53  # Proof object clause steps            : 38
% 2.30/2.53  # Proof object formula steps           : 19
% 2.30/2.53  # Proof object conjectures             : 32
% 2.30/2.53  # Proof object clause conjectures      : 29
% 2.30/2.53  # Proof object formula conjectures     : 3
% 2.30/2.53  # Proof object initial clauses used    : 16
% 2.30/2.53  # Proof object initial formulas used   : 9
% 2.30/2.53  # Proof object generating inferences   : 18
% 2.30/2.53  # Proof object simplifying inferences  : 49
% 2.30/2.53  # Training examples: 0 positive, 0 negative
% 2.30/2.53  # Parsed axioms                        : 9
% 2.30/2.53  # Removed by relevancy pruning/SinE    : 0
% 2.30/2.53  # Initial clauses                      : 21
% 2.30/2.53  # Removed in clause preprocessing      : 0
% 2.30/2.53  # Initial clauses in saturation        : 21
% 2.30/2.53  # Processed clauses                    : 6970
% 2.30/2.53  # ...of these trivial                  : 47
% 2.30/2.53  # ...subsumed                          : 6007
% 2.30/2.53  # ...remaining for further processing  : 916
% 2.30/2.53  # Other redundant clauses eliminated   : 0
% 2.30/2.53  # Clauses deleted for lack of memory   : 0
% 2.30/2.53  # Backward-subsumed                    : 56
% 2.30/2.53  # Backward-rewritten                   : 27
% 2.30/2.53  # Generated clauses                    : 171184
% 2.30/2.53  # ...of the previous two non-trivial   : 163940
% 2.30/2.53  # Contextual simplify-reflections      : 16
% 2.30/2.53  # Paramodulations                      : 171181
% 2.30/2.53  # Factorizations                       : 0
% 2.30/2.53  # Equation resolutions                 : 3
% 2.30/2.53  # Propositional unsat checks           : 0
% 2.30/2.53  #    Propositional check models        : 0
% 2.30/2.53  #    Propositional check unsatisfiable : 0
% 2.30/2.53  #    Propositional clauses             : 0
% 2.30/2.53  #    Propositional clauses after purity: 0
% 2.30/2.53  #    Propositional unsat core size     : 0
% 2.30/2.53  #    Propositional preprocessing time  : 0.000
% 2.30/2.53  #    Propositional encoding time       : 0.000
% 2.30/2.53  #    Propositional solver time         : 0.000
% 2.30/2.53  #    Success case prop preproc time    : 0.000
% 2.30/2.53  #    Success case prop encoding time   : 0.000
% 2.30/2.53  #    Success case prop solver time     : 0.000
% 2.30/2.53  # Current number of processed clauses  : 812
% 2.30/2.53  #    Positive orientable unit clauses  : 26
% 2.30/2.53  #    Positive unorientable unit clauses: 1
% 2.30/2.53  #    Negative unit clauses             : 1
% 2.30/2.53  #    Non-unit-clauses                  : 784
% 2.30/2.53  # Current number of unprocessed clauses: 156380
% 2.30/2.53  # ...number of literals in the above   : 970163
% 2.30/2.53  # Current number of archived formulas  : 0
% 2.30/2.53  # Current number of archived clauses   : 104
% 2.30/2.53  # Clause-clause subsumption calls (NU) : 315766
% 2.30/2.53  # Rec. Clause-clause subsumption calls : 124137
% 2.30/2.53  # Non-unit clause-clause subsumptions  : 6076
% 2.30/2.53  # Unit Clause-clause subsumption calls : 216
% 2.30/2.53  # Rewrite failures with RHS unbound    : 0
% 2.30/2.53  # BW rewrite match attempts            : 177
% 2.30/2.53  # BW rewrite match successes           : 50
% 2.30/2.53  # Condensation attempts                : 0
% 2.30/2.53  # Condensation successes               : 0
% 2.30/2.53  # Termbank termtop insertions          : 8773067
% 2.30/2.54  
% 2.30/2.54  # -------------------------------------------------
% 2.30/2.54  # User time                : 2.141 s
% 2.30/2.54  # System time              : 0.082 s
% 2.30/2.54  # Total time               : 2.223 s
% 2.30/2.54  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
