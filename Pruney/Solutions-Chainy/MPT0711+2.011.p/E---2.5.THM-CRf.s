%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:37 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 613 expanded)
%              Number of clauses        :   37 ( 231 expanded)
%              Number of leaves         :    8 ( 150 expanded)
%              Depth                    :   15
%              Number of atoms          :  183 (2857 expanded)
%              Number of equality atoms :   52 (1026 expanded)
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

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

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

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ r1_tarski(X14,k1_relat_1(X15))
      | k1_relat_1(k7_relat_1(X15,X14)) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X30] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & k1_relat_1(esk3_0) = k1_relat_1(esk4_0)
      & ( ~ r2_hidden(X30,esk5_0)
        | k1_funct_1(esk3_0,X30) = k1_funct_1(esk4_0,X30) )
      & k7_relat_1(esk3_0,esk5_0) != k7_relat_1(esk4_0,esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | r1_tarski(k1_relat_1(k7_relat_1(X11,X10)),X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k7_relat_1(X5,k1_relat_1(X6)) = k7_relat_1(X5,k1_relat_1(k7_relat_1(X6,k1_relat_1(X5)))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k7_relat_1(X1,k1_relat_1(X2)) = k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(k1_relat_1(k7_relat_1(X13,X12)),k1_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))) = k7_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_12]),c_0_13])])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_25,plain,(
    ! [X18,X19,X21] :
      ( v1_relat_1(esk1_2(X18,X19))
      & v1_funct_1(esk1_2(X18,X19))
      & k1_relat_1(esk1_2(X18,X19)) = X18
      & ( ~ r2_hidden(X21,X18)
        | k1_funct_1(esk1_2(X18,X19),X21) = X19 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_12]),c_0_13])])).

cnf(c_0_27,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1)))) = k7_relat_1(esk4_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_23]),c_0_24])])).

cnf(c_0_28,plain,
    ( k1_relat_1(esk1_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( v1_relat_1(esk1_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1)))) = k1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_26]),c_0_24])])).

cnf(c_0_31,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1))) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_33,plain,(
    ! [X22,X23,X24,X25] :
      ( ( k7_relat_1(X22,X24) != k7_relat_1(X23,X24)
        | ~ r2_hidden(X25,X24)
        | k1_funct_1(X22,X25) = k1_funct_1(X23,X25)
        | ~ r1_tarski(X24,k1_relat_1(X22))
        | ~ r1_tarski(X24,k1_relat_1(X23))
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X24)
        | k7_relat_1(X22,X24) = k7_relat_1(X23,X24)
        | ~ r1_tarski(X24,k1_relat_1(X22))
        | ~ r1_tarski(X24,k1_relat_1(X23))
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_funct_1(X22,esk2_3(X22,X23,X24)) != k1_funct_1(X23,esk2_3(X22,X23,X24))
        | k7_relat_1(X22,X24) = k7_relat_1(X23,X24)
        | ~ r1_tarski(X24,k1_relat_1(X22))
        | ~ r1_tarski(X24,k1_relat_1(X23))
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1)))) = k1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_22]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(X1))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_34]),c_0_12]),c_0_13])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))) = k7_relat_1(esk4_0,X1) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(X1)))) = k7_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_35])).

cnf(c_0_41,plain,
    ( k7_relat_1(X1,X3) = k7_relat_1(X2,X3)
    | k1_funct_1(X1,esk2_3(X1,X2,X3)) != k1_funct_1(X2,esk2_3(X1,X2,X3))
    | ~ r1_tarski(X3,k1_relat_1(X1))
    | ~ r1_tarski(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk3_0,X1) = k1_funct_1(esk4_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_44,plain,(
    ! [X7,X8,X9] :
      ( ( r2_hidden(X7,X8)
        | ~ r2_hidden(X7,k1_relat_1(k7_relat_1(X9,X8)))
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(X7,k1_relat_1(X9))
        | ~ r2_hidden(X7,k1_relat_1(k7_relat_1(X9,X8)))
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(X7,X8)
        | ~ r2_hidden(X7,k1_relat_1(X9))
        | r2_hidden(X7,k1_relat_1(k7_relat_1(X9,X8)))
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2))) = k7_relat_1(esk4_0,X2)
    | r2_hidden(esk2_3(X1,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(k7_relat_1(esk4_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_24])]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1))) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_29])])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(X2,X1)
    | k1_funct_1(esk4_0,esk2_3(esk3_0,X2,X1)) != k1_funct_1(X2,esk2_3(esk3_0,X2,X1))
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0))
    | ~ r1_tarski(X1,k1_relat_1(X2))
    | ~ r2_hidden(esk2_3(esk3_0,X2,X1),esk5_0)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_12]),c_0_13])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_12]),c_0_46]),c_0_43]),c_0_37]),c_0_13])])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(esk4_0,X1)
    | ~ r1_tarski(X1,k1_relat_1(esk4_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,X1),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_38]),c_0_24])])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk3_0,X1) = k7_relat_1(esk4_0,X1)
    | r2_hidden(esk2_3(esk3_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_24])])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk3_0,esk5_0) != k7_relat_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_46]),c_0_39]),c_0_37])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:31:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.71/2.87  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.71/2.87  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.71/2.87  #
% 2.71/2.87  # Preprocessing time       : 0.028 s
% 2.71/2.87  # Presaturation interreduction done
% 2.71/2.87  
% 2.71/2.87  # Proof found!
% 2.71/2.87  # SZS status Theorem
% 2.71/2.87  # SZS output start CNFRefutation
% 2.71/2.87  fof(t166_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 2.71/2.87  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.71/2.87  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.71/2.87  fof(t189_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.71/2.87  fof(t89_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 2.71/2.87  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.71/2.87  fof(t165_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((r1_tarski(X3,k1_relat_1(X1))&r1_tarski(X3,k1_relat_1(X2)))=>(k7_relat_1(X1,X3)=k7_relat_1(X2,X3)<=>![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 2.71/2.87  fof(t86_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))<=>(r2_hidden(X1,X2)&r2_hidden(X1,k1_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 2.71/2.87  fof(c_0_8, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((k1_relat_1(X1)=k1_relat_1(X2)&![X4]:(r2_hidden(X4,X3)=>k1_funct_1(X1,X4)=k1_funct_1(X2,X4)))=>k7_relat_1(X1,X3)=k7_relat_1(X2,X3))))), inference(assume_negation,[status(cth)],[t166_funct_1])).
% 2.71/2.87  fof(c_0_9, plain, ![X14, X15]:(~v1_relat_1(X15)|(~r1_tarski(X14,k1_relat_1(X15))|k1_relat_1(k7_relat_1(X15,X14))=X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 2.71/2.87  fof(c_0_10, negated_conjecture, ![X30]:((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((k1_relat_1(esk3_0)=k1_relat_1(esk4_0)&(~r2_hidden(X30,esk5_0)|k1_funct_1(esk3_0,X30)=k1_funct_1(esk4_0,X30)))&k7_relat_1(esk3_0,esk5_0)!=k7_relat_1(esk4_0,esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])).
% 2.71/2.87  cnf(c_0_11, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.71/2.87  cnf(c_0_12, negated_conjecture, (k1_relat_1(esk3_0)=k1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.71/2.87  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.71/2.87  fof(c_0_14, plain, ![X10, X11]:(~v1_relat_1(X11)|r1_tarski(k1_relat_1(k7_relat_1(X11,X10)),X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 2.71/2.87  fof(c_0_15, plain, ![X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|k7_relat_1(X5,k1_relat_1(X6))=k7_relat_1(X5,k1_relat_1(k7_relat_1(X6,k1_relat_1(X5)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t189_relat_1])])])).
% 2.71/2.87  cnf(c_0_16, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 2.71/2.88  cnf(c_0_17, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.71/2.88  cnf(c_0_18, plain, (k7_relat_1(X1,k1_relat_1(X2))=k7_relat_1(X1,k1_relat_1(k7_relat_1(X2,k1_relat_1(X1))))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.71/2.88  fof(c_0_19, plain, ![X12, X13]:(~v1_relat_1(X13)|r1_tarski(k1_relat_1(k7_relat_1(X13,X12)),k1_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t89_relat_1])])).
% 2.71/2.88  cnf(c_0_20, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))))=k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 2.71/2.88  cnf(c_0_21, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0))))=k7_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_12]), c_0_13])])).
% 2.71/2.88  cnf(c_0_22, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.71/2.88  cnf(c_0_23, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1)))=k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 2.71/2.88  cnf(c_0_24, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.71/2.88  fof(c_0_25, plain, ![X18, X19, X21]:(((v1_relat_1(esk1_2(X18,X19))&v1_funct_1(esk1_2(X18,X19)))&k1_relat_1(esk1_2(X18,X19))=X18)&(~r2_hidden(X21,X18)|k1_funct_1(esk1_2(X18,X19),X21)=X19)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 2.71/2.88  cnf(c_0_26, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk3_0,X1)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_12]), c_0_13])])).
% 2.71/2.88  cnf(c_0_27, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(X1))))=k7_relat_1(esk4_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_23]), c_0_24])])).
% 2.71/2.88  cnf(c_0_28, plain, (k1_relat_1(esk1_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.71/2.88  cnf(c_0_29, plain, (v1_relat_1(esk1_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.71/2.88  cnf(c_0_30, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1))))=k1_relat_1(k7_relat_1(esk3_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_26]), c_0_24])])).
% 2.71/2.88  cnf(c_0_31, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk3_0,X1)))=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 2.71/2.88  cnf(c_0_32, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 2.71/2.88  fof(c_0_33, plain, ![X22, X23, X24, X25]:((k7_relat_1(X22,X24)!=k7_relat_1(X23,X24)|(~r2_hidden(X25,X24)|k1_funct_1(X22,X25)=k1_funct_1(X23,X25))|(~r1_tarski(X24,k1_relat_1(X22))|~r1_tarski(X24,k1_relat_1(X23)))|(~v1_relat_1(X23)|~v1_funct_1(X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&((r2_hidden(esk2_3(X22,X23,X24),X24)|k7_relat_1(X22,X24)=k7_relat_1(X23,X24)|(~r1_tarski(X24,k1_relat_1(X22))|~r1_tarski(X24,k1_relat_1(X23)))|(~v1_relat_1(X23)|~v1_funct_1(X23))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k1_funct_1(X22,esk2_3(X22,X23,X24))!=k1_funct_1(X23,esk2_3(X22,X23,X24))|k7_relat_1(X22,X24)=k7_relat_1(X23,X24)|(~r1_tarski(X24,k1_relat_1(X22))|~r1_tarski(X24,k1_relat_1(X23)))|(~v1_relat_1(X23)|~v1_funct_1(X23))|(~v1_relat_1(X22)|~v1_funct_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t165_funct_1])])])])])).
% 2.71/2.88  cnf(c_0_34, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1))))=k1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_22]), c_0_24])])).
% 2.71/2.88  cnf(c_0_35, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(X1)))=k1_relat_1(k7_relat_1(X1,k1_relat_1(esk4_0)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_23, c_0_32])).
% 2.71/2.88  cnf(c_0_36, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.71/2.88  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_34]), c_0_12]), c_0_13])])).
% 2.71/2.88  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.71/2.88  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1)))=k7_relat_1(esk4_0,X1)), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 2.71/2.88  cnf(c_0_40, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,k1_relat_1(X1))))=k7_relat_1(esk3_0,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_35])).
% 2.71/2.88  cnf(c_0_41, plain, (k7_relat_1(X1,X3)=k7_relat_1(X2,X3)|k1_funct_1(X1,esk2_3(X1,X2,X3))!=k1_funct_1(X2,esk2_3(X1,X2,X3))|~r1_tarski(X3,k1_relat_1(X1))|~r1_tarski(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 2.71/2.88  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk3_0,X1)=k1_funct_1(esk4_0,X1)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.71/2.88  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.71/2.88  fof(c_0_44, plain, ![X7, X8, X9]:(((r2_hidden(X7,X8)|~r2_hidden(X7,k1_relat_1(k7_relat_1(X9,X8)))|~v1_relat_1(X9))&(r2_hidden(X7,k1_relat_1(X9))|~r2_hidden(X7,k1_relat_1(k7_relat_1(X9,X8)))|~v1_relat_1(X9)))&(~r2_hidden(X7,X8)|~r2_hidden(X7,k1_relat_1(X9))|r2_hidden(X7,k1_relat_1(k7_relat_1(X9,X8)))|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_relat_1])])])).
% 2.71/2.88  cnf(c_0_45, negated_conjecture, (k7_relat_1(X1,k1_relat_1(k7_relat_1(esk4_0,X2)))=k7_relat_1(esk4_0,X2)|r2_hidden(esk2_3(X1,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X2))),k1_relat_1(k7_relat_1(esk4_0,X2)))|~v1_funct_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X2)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_24])]), c_0_39])).
% 2.71/2.88  cnf(c_0_46, negated_conjecture, (k7_relat_1(esk3_0,k1_relat_1(k7_relat_1(esk4_0,X1)))=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_28]), c_0_29])])).
% 2.71/2.88  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(X2,X1)|k1_funct_1(esk4_0,esk2_3(esk3_0,X2,X1))!=k1_funct_1(X2,esk2_3(esk3_0,X2,X1))|~v1_funct_1(X2)|~r1_tarski(X1,k1_relat_1(esk4_0))|~r1_tarski(X1,k1_relat_1(X2))|~r2_hidden(esk2_3(esk3_0,X2,X1),esk5_0)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_12]), c_0_13])])).
% 2.71/2.88  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 2.71/2.88  cnf(c_0_49, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(esk4_0,X1)|r2_hidden(esk2_3(esk3_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),k1_relat_1(k7_relat_1(esk4_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_12]), c_0_46]), c_0_43]), c_0_37]), c_0_13])])).
% 2.71/2.88  cnf(c_0_50, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(esk4_0,X1)|~r1_tarski(X1,k1_relat_1(esk4_0))|~r2_hidden(esk2_3(esk3_0,esk4_0,X1),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_38]), c_0_24])])).
% 2.71/2.88  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk3_0,X1)=k7_relat_1(esk4_0,X1)|r2_hidden(esk2_3(esk3_0,esk4_0,k1_relat_1(k7_relat_1(esk4_0,X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_24])])).
% 2.71/2.88  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk3_0,esk5_0)!=k7_relat_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.71/2.88  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_46]), c_0_39]), c_0_37])]), c_0_52]), ['proof']).
% 2.71/2.88  # SZS output end CNFRefutation
% 2.71/2.88  # Proof object total steps             : 54
% 2.71/2.88  # Proof object clause steps            : 37
% 2.71/2.88  # Proof object formula steps           : 17
% 2.71/2.88  # Proof object conjectures             : 31
% 2.71/2.88  # Proof object clause conjectures      : 28
% 2.71/2.88  # Proof object formula conjectures     : 3
% 2.71/2.88  # Proof object initial clauses used    : 16
% 2.71/2.88  # Proof object initial formulas used   : 8
% 2.71/2.88  # Proof object generating inferences   : 18
% 2.71/2.88  # Proof object simplifying inferences  : 45
% 2.71/2.88  # Training examples: 0 positive, 0 negative
% 2.71/2.88  # Parsed axioms                        : 9
% 2.71/2.88  # Removed by relevancy pruning/SinE    : 0
% 2.71/2.88  # Initial clauses                      : 22
% 2.71/2.88  # Removed in clause preprocessing      : 0
% 2.71/2.88  # Initial clauses in saturation        : 22
% 2.71/2.88  # Processed clauses                    : 9483
% 2.71/2.88  # ...of these trivial                  : 68
% 2.71/2.88  # ...subsumed                          : 8443
% 2.71/2.88  # ...remaining for further processing  : 972
% 2.71/2.88  # Other redundant clauses eliminated   : 2
% 2.71/2.88  # Clauses deleted for lack of memory   : 0
% 2.71/2.88  # Backward-subsumed                    : 69
% 2.71/2.88  # Backward-rewritten                   : 39
% 2.71/2.88  # Generated clauses                    : 182892
% 2.71/2.88  # ...of the previous two non-trivial   : 176123
% 2.71/2.88  # Contextual simplify-reflections      : 7
% 2.71/2.88  # Paramodulations                      : 182887
% 2.71/2.88  # Factorizations                       : 0
% 2.71/2.88  # Equation resolutions                 : 5
% 2.71/2.88  # Propositional unsat checks           : 0
% 2.71/2.88  #    Propositional check models        : 0
% 2.71/2.88  #    Propositional check unsatisfiable : 0
% 2.71/2.88  #    Propositional clauses             : 0
% 2.71/2.88  #    Propositional clauses after purity: 0
% 2.71/2.88  #    Propositional unsat core size     : 0
% 2.71/2.88  #    Propositional preprocessing time  : 0.000
% 2.71/2.88  #    Propositional encoding time       : 0.000
% 2.71/2.88  #    Propositional solver time         : 0.000
% 2.71/2.88  #    Success case prop preproc time    : 0.000
% 2.71/2.88  #    Success case prop encoding time   : 0.000
% 2.71/2.88  #    Success case prop solver time     : 0.000
% 2.71/2.88  # Current number of processed clauses  : 842
% 2.71/2.88  #    Positive orientable unit clauses  : 24
% 2.71/2.88  #    Positive unorientable unit clauses: 0
% 2.71/2.88  #    Negative unit clauses             : 1
% 2.71/2.88  #    Non-unit-clauses                  : 817
% 2.71/2.88  # Current number of unprocessed clauses: 165698
% 2.71/2.88  # ...number of literals in the above   : 1082080
% 2.71/2.88  # Current number of archived formulas  : 0
% 2.71/2.88  # Current number of archived clauses   : 130
% 2.71/2.88  # Clause-clause subsumption calls (NU) : 371734
% 2.71/2.88  # Rec. Clause-clause subsumption calls : 148581
% 2.71/2.88  # Non-unit clause-clause subsumptions  : 8519
% 2.71/2.88  # Unit Clause-clause subsumption calls : 431
% 2.71/2.88  # Rewrite failures with RHS unbound    : 0
% 2.71/2.88  # BW rewrite match attempts            : 321
% 2.71/2.88  # BW rewrite match successes           : 27
% 2.71/2.88  # Condensation attempts                : 0
% 2.71/2.88  # Condensation successes               : 0
% 2.71/2.88  # Termbank termtop insertions          : 9085907
% 2.71/2.88  
% 2.71/2.88  # -------------------------------------------------
% 2.71/2.88  # User time                : 2.463 s
% 2.71/2.88  # System time              : 0.081 s
% 2.71/2.88  # Total time               : 2.544 s
% 2.71/2.88  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
