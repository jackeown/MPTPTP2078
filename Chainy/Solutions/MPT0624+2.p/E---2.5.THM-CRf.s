%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0624+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   21 (  47 expanded)
%              Number of clauses        :   14 (  18 expanded)
%              Number of leaves         :    3 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 198 expanded)
%              Number of equality atoms :    5 (  23 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t19_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & ! [X4] :
                  ~ ( r2_hidden(X4,k1_relat_1(X2))
                    & X3 = k1_funct_1(X2,X4) ) )
       => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & ! [X4] :
                    ~ ( r2_hidden(X4,k1_relat_1(X2))
                      & X3 = k1_funct_1(X2,X4) ) )
         => r1_tarski(X1,k2_relat_1(X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t19_funct_1])).

fof(c_0_4,negated_conjecture,(
    ! [X2765] :
      ( v1_relat_1(esk171_0)
      & v1_funct_1(esk171_0)
      & ( r2_hidden(esk172_1(X2765),k1_relat_1(esk171_0))
        | ~ r2_hidden(X2765,esk170_0) )
      & ( X2765 = k1_funct_1(esk171_0,esk172_1(X2765))
        | ~ r2_hidden(X2765,esk170_0) )
      & ~ r1_tarski(esk170_0,k2_relat_1(esk171_0)) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

fof(c_0_5,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X2747,X2748] :
      ( ~ v1_relat_1(X2748)
      | ~ v1_funct_1(X2748)
      | ~ r2_hidden(X2747,k1_relat_1(X2748))
      | r2_hidden(k1_funct_1(X2748,X2747),k2_relat_1(X2748)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_7,negated_conjecture,
    ( ~ r1_tarski(esk170_0,k2_relat_1(esk171_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk171_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk171_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( X1 = k1_funct_1(esk171_0,esk172_1(X1))
    | ~ r2_hidden(X1,esk170_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk2_2(esk170_0,k2_relat_1(esk171_0)),esk170_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk171_0,X1),k2_relat_1(esk171_0))
    | ~ r2_hidden(X1,k1_relat_1(esk171_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( k1_funct_1(esk171_0,esk172_1(esk2_2(esk170_0,k2_relat_1(esk171_0)))) = esk2_2(esk170_0,k2_relat_1(esk171_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( ~ r2_hidden(esk2_2(esk170_0,k2_relat_1(esk171_0)),k2_relat_1(esk171_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk172_1(esk2_2(esk170_0,k2_relat_1(esk171_0))),k1_relat_1(esk171_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk172_1(X1),k1_relat_1(esk171_0))
    | ~ r2_hidden(X1,esk170_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13])]),
    [proof]).
%------------------------------------------------------------------------------
