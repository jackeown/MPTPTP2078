%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t99_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 35.30s
% Output     : CNFRefutation 35.30s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 124 expanded)
%              Number of clauses        :   26 (  50 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  247 ( 931 expanded)
%              Number of equality atoms :   39 ( 127 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   79 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( X2 = k8_relat_1(X1,X3)
          <=> ( ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(X4,k1_relat_1(X3))
                    & r2_hidden(k1_funct_1(X3,X4),X1) ) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t99_funct_1.p',t85_funct_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t99_funct_1.p',dt_k8_relat_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t99_funct_1.p',fc9_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t99_funct_1.p',d8_funct_1)).

fof(t99_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => v2_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t99_funct_1.p',t99_funct_1)).

fof(c_0_5,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( r2_hidden(X28,k1_relat_1(X27))
        | ~ r2_hidden(X28,k1_relat_1(X26))
        | X26 != k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(k1_funct_1(X27,X28),X25)
        | ~ r2_hidden(X28,k1_relat_1(X26))
        | X26 != k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X29,k1_relat_1(X27))
        | ~ r2_hidden(k1_funct_1(X27,X29),X25)
        | r2_hidden(X29,k1_relat_1(X26))
        | X26 != k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X30,k1_relat_1(X26))
        | k1_funct_1(X26,X30) = k1_funct_1(X27,X30)
        | X26 != k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk7_3(X25,X26,X27),k1_relat_1(X26))
        | ~ r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X26))
        | ~ r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X27))
        | ~ r2_hidden(k1_funct_1(X27,esk6_3(X25,X26,X27)),X25)
        | X26 = k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k1_funct_1(X26,esk7_3(X25,X26,X27)) != k1_funct_1(X27,esk7_3(X25,X26,X27))
        | ~ r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X26))
        | ~ r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X27))
        | ~ r2_hidden(k1_funct_1(X27,esk6_3(X25,X26,X27)),X25)
        | X26 = k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk7_3(X25,X26,X27),k1_relat_1(X26))
        | r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X27))
        | r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X26))
        | X26 = k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k1_funct_1(X26,esk7_3(X25,X26,X27)) != k1_funct_1(X27,esk7_3(X25,X26,X27))
        | r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X27))
        | r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X26))
        | X26 = k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk7_3(X25,X26,X27),k1_relat_1(X26))
        | r2_hidden(k1_funct_1(X27,esk6_3(X25,X26,X27)),X25)
        | r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X26))
        | X26 = k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k1_funct_1(X26,esk7_3(X25,X26,X27)) != k1_funct_1(X27,esk7_3(X25,X26,X27))
        | r2_hidden(k1_funct_1(X27,esk6_3(X25,X26,X27)),X25)
        | r2_hidden(esk6_3(X25,X26,X27),k1_relat_1(X26))
        | X26 = k8_relat_1(X25,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

fof(c_0_6,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | v1_relat_1(k8_relat_1(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_7,plain,(
    ! [X35,X36] :
      ( ( v1_relat_1(k8_relat_1(X35,X36))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( v1_funct_1(k8_relat_1(X35,X36))
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

cnf(c_0_8,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X2 != k8_relat_1(X4,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_funct_1(k8_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_funct_1(X9)
        | ~ r2_hidden(X10,k1_relat_1(X9))
        | ~ r2_hidden(X11,k1_relat_1(X9))
        | k1_funct_1(X9,X10) != k1_funct_1(X9,X11)
        | X10 = X11
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk3_1(X9),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk4_1(X9),k1_relat_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( k1_funct_1(X9,esk3_1(X9)) = k1_funct_1(X9,esk4_1(X9))
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk3_1(X9) != esk4_1(X9)
        | v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | X3 != k8_relat_1(X4,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),X3) = k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(k8_relat_1(X1,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9]),c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_9]),c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k1_funct_1(X1,esk3_1(X1)) = k1_funct_1(X1,esk4_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),esk3_1(k8_relat_1(X1,X2))) = k1_funct_1(X2,esk3_1(k8_relat_1(X1,X2)))
    | v2_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_9]),c_0_10])).

cnf(c_0_19,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_1(k8_relat_1(X1,X2)),k1_relat_1(X2))
    | v2_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_9]),c_0_10])).

cnf(c_0_21,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),esk4_1(k8_relat_1(X1,X2))) = k1_funct_1(X2,esk4_1(k8_relat_1(X1,X2)))
    | v2_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_16]),c_0_9]),c_0_10])).

cnf(c_0_22,plain,
    ( k1_funct_1(k8_relat_1(X1,X2),esk4_1(k8_relat_1(X1,X2))) = k1_funct_1(X2,esk3_1(k8_relat_1(X1,X2)))
    | v2_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_9]),c_0_10])).

cnf(c_0_23,plain,
    ( X1 = esk4_1(k8_relat_1(X2,X3))
    | v2_funct_1(k8_relat_1(X2,X3))
    | k1_funct_1(X3,X1) != k1_funct_1(X3,esk4_1(k8_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( k1_funct_1(X1,esk3_1(k8_relat_1(X2,X1))) = k1_funct_1(X1,esk4_1(k8_relat_1(X2,X1)))
    | v2_funct_1(k8_relat_1(X2,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_1(k8_relat_1(X1,X2)),k1_relat_1(X2))
    | v2_funct_1(k8_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_14]),c_0_9]),c_0_10])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
         => v2_funct_1(k8_relat_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t99_funct_1])).

cnf(c_0_27,plain,
    ( esk3_1(k8_relat_1(X1,X2)) = esk4_1(k8_relat_1(X3,X2))
    | v2_funct_1(k8_relat_1(X1,X2))
    | v2_funct_1(k8_relat_1(X3,X2))
    | k1_funct_1(X2,esk4_1(k8_relat_1(X1,X2))) != k1_funct_1(X2,esk4_1(k8_relat_1(X3,X2)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_28,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & v2_funct_1(esk2_0)
    & ~ v2_funct_1(k8_relat_1(esk1_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_29,plain,
    ( v2_funct_1(X1)
    | esk3_1(X1) != esk4_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,plain,
    ( esk3_1(k8_relat_1(X1,X2)) = esk4_1(k8_relat_1(X1,X2))
    | v2_funct_1(k8_relat_1(X1,X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_funct_1(k8_relat_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( v2_funct_1(k8_relat_1(X1,X2))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_9]),c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
