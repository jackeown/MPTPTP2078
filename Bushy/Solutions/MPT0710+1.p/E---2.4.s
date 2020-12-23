%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t165_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:19 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 (1545 expanded)
%              Number of clauses        :   43 ( 612 expanded)
%              Number of leaves         :    8 ( 373 expanded)
%              Depth                    :   18
%              Number of atoms          :  182 (8170 expanded)
%              Number of equality atoms :   71 (2441 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t165_funct_1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',t165_funct_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',dt_k7_relat_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',t90_relat_1)).

fof(t9_funct_1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',t9_funct_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',t28_xboole_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t165_funct_1.p',t72_funct_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t165_funct_1])).

fof(c_0_9,plain,(
    ! [X47,X48] :
      ( ( v1_relat_1(k7_relat_1(X47,X48))
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( v1_funct_1(k7_relat_1(X47,X48))
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_10,negated_conjecture,(
    ! [X9] :
      ( v1_relat_1(esk1_0)
      & v1_funct_1(esk1_0)
      & v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & r1_tarski(esk3_0,k1_relat_1(esk1_0))
      & r1_tarski(esk3_0,k1_relat_1(esk2_0))
      & ( r2_hidden(esk4_0,esk3_0)
        | k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) )
      & ( k1_funct_1(esk1_0,esk4_0) != k1_funct_1(esk2_0,esk4_0)
        | k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) )
      & ( k7_relat_1(esk1_0,esk3_0) = k7_relat_1(esk2_0,esk3_0)
        | ~ r2_hidden(X9,esk3_0)
        | k1_funct_1(esk1_0,X9) = k1_funct_1(esk2_0,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | v1_relat_1(k7_relat_1(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_12,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X43)
      | k1_relat_1(k7_relat_1(X43,X42)) = k3_xboole_0(k1_relat_1(X43),X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_13,plain,(
    ! [X44,X45] :
      ( ( r2_hidden(esk6_2(X44,X45),k1_relat_1(X44))
        | k1_relat_1(X44) != k1_relat_1(X45)
        | X44 = X45
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( k1_funct_1(X44,esk6_2(X44,X45)) != k1_funct_1(X45,esk6_2(X44,X45))
        | k1_relat_1(X44) != k1_relat_1(X45)
        | X44 = X45
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_14,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk6_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,X1)) = k3_xboole_0(k1_relat_1(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

fof(c_0_23,plain,(
    ! [X12,X13] : k3_xboole_0(X12,X13) = k3_xboole_0(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_24,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(X21,X22)
      | k3_xboole_0(X21,X22) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k7_relat_1(esk2_0,X2)
    | r2_hidden(esk6_2(X1,k7_relat_1(esk2_0,X2)),k1_relat_1(X1))
    | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(esk2_0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k7_relat_1(esk2_0,X2)
    | r2_hidden(esk6_2(X1,k7_relat_1(esk2_0,X2)),k1_relat_1(X1))
    | k1_relat_1(X1) != k3_xboole_0(X2,k1_relat_1(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk3_0,k1_relat_1(esk2_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( X1 = k7_relat_1(esk2_0,esk3_0)
    | r2_hidden(esk6_2(X1,k7_relat_1(esk2_0,esk3_0)),k1_relat_1(X1))
    | k1_relat_1(X1) != esk3_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk1_0,X1)) = k3_xboole_0(k1_relat_1(esk1_0),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_32]),c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( k7_relat_1(esk1_0,X1) = k7_relat_1(esk2_0,esk3_0)
    | r2_hidden(esk6_2(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,esk3_0)),k3_xboole_0(k1_relat_1(esk1_0),X1))
    | k3_xboole_0(k1_relat_1(esk1_0),X1) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_39,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ r2_hidden(X35,X36)
      | k1_funct_1(k7_relat_1(X37,X36),X35) = k1_funct_1(X37,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(esk1_0,X1) = k7_relat_1(esk2_0,esk3_0)
    | r2_hidden(esk6_2(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,esk3_0)),k3_xboole_0(X1,k1_relat_1(esk1_0)))
    | k3_xboole_0(X1,k1_relat_1(esk1_0)) != esk3_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk3_0,k1_relat_1(esk1_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_38])).

cnf(c_0_42,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k7_relat_1(esk2_0,esk3_0) = k7_relat_1(esk1_0,esk3_0)
    | r2_hidden(esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_44,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk6_2(X1,X2)) != k1_funct_1(X2,esk6_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,esk3_0),esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) = k1_funct_1(X1,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0)))
    | k7_relat_1(esk2_0,esk3_0) = k7_relat_1(esk1_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k7_relat_1(esk2_0,X2)
    | k1_funct_1(X1,esk6_2(X1,k7_relat_1(esk2_0,X2))) != k1_funct_1(k7_relat_1(esk2_0,X2),esk6_2(X1,k7_relat_1(esk2_0,X2)))
    | k1_relat_1(X1) != k3_xboole_0(k1_relat_1(esk2_0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk3_0),esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) = k1_funct_1(esk2_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0)))
    | k7_relat_1(esk2_0,esk3_0) = k7_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_15]),c_0_16])])).

cnf(c_0_48,negated_conjecture,
    ( k7_relat_1(esk1_0,esk3_0) = k7_relat_1(esk2_0,esk3_0)
    | k1_funct_1(esk1_0,X1) = k1_funct_1(esk2_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(esk2_0,esk3_0) = k7_relat_1(esk1_0,esk3_0)
    | k1_funct_1(k7_relat_1(esk1_0,esk3_0),esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) != k1_funct_1(esk2_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_34]),c_0_35]),c_0_36])]),c_0_26]),c_0_30]),c_0_26]),c_0_41])])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk1_0,esk3_0),esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) = k1_funct_1(esk1_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0)))
    | k7_relat_1(esk2_0,esk3_0) = k7_relat_1(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_31])])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk2_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) = k1_funct_1(esk1_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0)))
    | k7_relat_1(esk2_0,esk3_0) = k7_relat_1(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk2_0,esk3_0) = k7_relat_1(esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(k7_relat_1(X1,esk3_0),esk4_0) = k1_funct_1(X1,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk1_0,esk4_0) != k1_funct_1(esk2_0,esk4_0)
    | k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk1_0,esk3_0),esk4_0) = k1_funct_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_15]),c_0_53]),c_0_16])])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk2_0,esk4_0) != k1_funct_1(esk1_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_32]),c_0_31])]),c_0_57]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
