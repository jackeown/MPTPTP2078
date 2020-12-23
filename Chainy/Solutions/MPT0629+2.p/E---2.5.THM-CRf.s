%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0629+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:49 EST 2020

% Result     : Theorem 10.49s
% Output     : CNFRefutation 10.49s
% Verified   : 
% Statistics : Number of formulae       :   21 (  34 expanded)
%              Number of clauses        :   12 (  13 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 ( 130 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))
           => r2_hidden(X1,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t160_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t144_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT001+2.ax',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k2_relat_1(k5_relat_1(X3,X2)))
             => r2_hidden(X1,k2_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_funct_1])).

fof(c_0_5,plain,(
    ! [X2432,X2433] :
      ( ~ v1_relat_1(X2432)
      | ~ v1_relat_1(X2433)
      | k2_relat_1(k5_relat_1(X2432,X2433)) = k9_relat_1(X2433,k2_relat_1(X2432)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk174_0)
    & v1_funct_1(esk174_0)
    & v1_relat_1(esk175_0)
    & v1_funct_1(esk175_0)
    & r2_hidden(esk173_0,k2_relat_1(k5_relat_1(esk175_0,esk174_0)))
    & ~ r2_hidden(esk173_0,k2_relat_1(esk174_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk174_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X2391,X2392] :
      ( ~ v1_relat_1(X2392)
      | r1_tarski(k9_relat_1(X2392,X2391),k2_relat_1(X2392)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_10,negated_conjecture,
    ( k9_relat_1(esk174_0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,esk174_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk175_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( ~ r1_tarski(X27,X28)
        | ~ r2_hidden(X29,X27)
        | r2_hidden(X29,X28) )
      & ( r2_hidden(esk2_2(X30,X31),X30)
        | r1_tarski(X30,X31) )
      & ( ~ r2_hidden(esk2_2(X30,X31),X31)
        | r1_tarski(X30,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k9_relat_1(esk174_0,k2_relat_1(esk175_0)) = k2_relat_1(k5_relat_1(esk175_0,esk174_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk175_0,esk174_0)),k2_relat_1(esk174_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_8])])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk174_0))
    | ~ r2_hidden(X1,k2_relat_1(k5_relat_1(esk175_0,esk174_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk173_0,k2_relat_1(k5_relat_1(esk175_0,esk174_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk173_0,k2_relat_1(esk174_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
