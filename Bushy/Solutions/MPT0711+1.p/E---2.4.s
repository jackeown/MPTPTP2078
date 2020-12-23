%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t166_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:19 EDT 2019

% Result     : Theorem 152.71s
% Output     : CNFRefutation 152.71s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 368 expanded)
%              Number of clauses        :   33 ( 137 expanded)
%              Number of leaves         :    7 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 (1793 expanded)
%              Number of equality atoms :   52 ( 613 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/funct_1__t166_funct_1.p',t166_funct_1)).

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t166_funct_1.p',t90_relat_1)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t166_funct_1.p',fc8_funct_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t166_funct_1.p',dt_k7_relat_1)).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t166_funct_1.p',t9_funct_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t166_funct_1.p',d4_xboole_0)).

fof(t70_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k7_relat_1(X3,X2)))
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t166_funct_1.p',t70_funct_1)).

fof(c_0_7,negated_conjecture,(
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

fof(c_0_8,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | k1_relat_1(k7_relat_1(X41,X40)) = k3_xboole_0(k1_relat_1(X41),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X8] :
      ( v1_relat_1(esk1_0)
      & v1_funct_1(esk1_0)
      & v1_relat_1(esk2_0)
      & v1_funct_1(esk2_0)
      & k1_relat_1(esk1_0) = k1_relat_1(esk2_0)
      & ( ~ r2_hidden(X8,esk3_0)
        | k1_funct_1(esk1_0,X8) = k1_funct_1(esk2_0,X8) )
      & k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X45,X46] :
      ( ( v1_relat_1(k7_relat_1(X45,X46))
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( v1_funct_1(k7_relat_1(X45,X46))
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_11,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | v1_relat_1(k7_relat_1(X22,X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_12,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k1_relat_1(esk1_0) = k1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_15,plain,(
    ! [X42,X43] :
      ( ( r2_hidden(esk6_2(X42,X43),k1_relat_1(X42))
        | k1_relat_1(X42) != k1_relat_1(X43)
        | X42 = X43
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( k1_funct_1(X42,esk6_2(X42,X43)) != k1_funct_1(X43,esk6_2(X42,X43))
        | k1_relat_1(X42) != k1_relat_1(X43)
        | X42 = X43
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_16,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk1_0),X1) = k1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_21,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk4_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk4_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk4_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk4_3(X18,X19,X20),X18)
        | r2_hidden(esk4_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk4_3(X18,X19,X20),X19)
        | r2_hidden(esk4_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk6_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13])])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk2_0,X1)) = k1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( X1 = k7_relat_1(esk2_0,X2)
    | r2_hidden(esk6_2(X1,k7_relat_1(esk2_0,X2)),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(k7_relat_1(esk1_0,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_26]),c_0_19])])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk1_0),X1) = k1_relat_1(k7_relat_1(esk1_0,X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(esk1_0,esk3_0) != k7_relat_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k7_relat_1(esk2_0,X1) = k7_relat_1(esk1_0,X1)
    | r2_hidden(esk6_2(k7_relat_1(esk1_0,X1),k7_relat_1(esk2_0,X1)),k1_relat_1(k7_relat_1(esk1_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_29]),c_0_30])])).

fof(c_0_35,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ r2_hidden(X33,k1_relat_1(k7_relat_1(X35,X34)))
      | k1_funct_1(k7_relat_1(X35,X34),X33) = k1_funct_1(X35,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t70_funct_1])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(esk1_0,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0)),k1_relat_1(k7_relat_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk1_0,X1) = k1_funct_1(esk2_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk6_2(X1,X2)) != k1_funct_1(X2,esk6_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,X1),X2) = k1_funct_1(esk2_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(k7_relat_1(esk1_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_25]),c_0_17]),c_0_13])])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk2_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) = k1_funct_1(esk1_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( X1 = k7_relat_1(esk2_0,X2)
    | k1_funct_1(X1,esk6_2(X1,k7_relat_1(esk2_0,X2))) != k1_funct_1(k7_relat_1(esk2_0,X2),esk6_2(X1,k7_relat_1(esk2_0,X2)))
    | k1_relat_1(X1) != k1_relat_1(k7_relat_1(esk1_0,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk2_0,esk3_0),esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) = k1_funct_1(esk1_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_37]),c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk1_0,esk3_0),esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) = k1_funct_1(esk1_0,esk6_2(k7_relat_1(esk1_0,esk3_0),k7_relat_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_26]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_29]),c_0_30])]),c_0_33]),
    [proof]).
%------------------------------------------------------------------------------
