%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t89_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:28 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   23 (  31 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 181 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   3 average)
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',t85_funct_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',dt_k8_relat_1)).

fof(fc9_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k8_relat_1(X1,X2))
        & v1_funct_1(k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',fc9_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',d3_tarski)).

fof(t89_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t89_funct_1.p',t89_funct_1)).

fof(c_0_5,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( r2_hidden(X37,k1_relat_1(X36))
        | ~ r2_hidden(X37,k1_relat_1(X35))
        | X35 != k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(k1_funct_1(X36,X37),X34)
        | ~ r2_hidden(X37,k1_relat_1(X35))
        | X35 != k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X38,k1_relat_1(X36))
        | ~ r2_hidden(k1_funct_1(X36,X38),X34)
        | r2_hidden(X38,k1_relat_1(X35))
        | X35 != k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X39,k1_relat_1(X35))
        | k1_funct_1(X35,X39) = k1_funct_1(X36,X39)
        | X35 != k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),k1_relat_1(X35))
        | ~ r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X35))
        | ~ r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X36))
        | ~ r2_hidden(k1_funct_1(X36,esk5_3(X34,X35,X36)),X34)
        | X35 = k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( k1_funct_1(X35,esk6_3(X34,X35,X36)) != k1_funct_1(X36,esk6_3(X34,X35,X36))
        | ~ r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X35))
        | ~ r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X36))
        | ~ r2_hidden(k1_funct_1(X36,esk5_3(X34,X35,X36)),X34)
        | X35 = k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),k1_relat_1(X35))
        | r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X36))
        | r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X35))
        | X35 = k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( k1_funct_1(X35,esk6_3(X34,X35,X36)) != k1_funct_1(X36,esk6_3(X34,X35,X36))
        | r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X36))
        | r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X35))
        | X35 = k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),k1_relat_1(X35))
        | r2_hidden(k1_funct_1(X36,esk5_3(X34,X35,X36)),X34)
        | r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X35))
        | X35 = k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( k1_funct_1(X35,esk6_3(X34,X35,X36)) != k1_funct_1(X36,esk6_3(X34,X35,X36))
        | r2_hidden(k1_funct_1(X36,esk5_3(X34,X35,X36)),X34)
        | r2_hidden(esk5_3(X34,X35,X36),k1_relat_1(X35))
        | X35 = k8_relat_1(X34,X36)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_funct_1])])])])])])).

fof(c_0_6,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | v1_relat_1(k8_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_7,plain,(
    ! [X44,X45] :
      ( ( v1_relat_1(k8_relat_1(X44,X45))
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( v1_funct_1(k8_relat_1(X44,X45))
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_funct_1])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | X3 != k8_relat_1(X4,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
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
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk3_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk3_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t89_funct_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X3,X2)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9]),c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ~ r1_tarski(k1_relat_1(k8_relat_1(esk1_0,esk2_0)),k1_relat_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_2(k1_relat_1(k8_relat_1(X1,X2)),X3),k1_relat_1(X2))
    | r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k8_relat_1(esk1_0,esk2_0)),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_relat_1(k8_relat_1(X1,X2)),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),
    [proof]).
%------------------------------------------------------------------------------
