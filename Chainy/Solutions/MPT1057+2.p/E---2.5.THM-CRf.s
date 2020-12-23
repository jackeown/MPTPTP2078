%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1057+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:01 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   11 (  17 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    2 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  51 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t174_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(X3,X2)
         => k9_relat_1(X1,X3) = k9_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_2)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',t162_relat_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(X3,X2)
           => k9_relat_1(X1,X3) = k9_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t174_funct_2])).

fof(c_0_3,plain,(
    ! [X77,X78,X79] :
      ( ~ v1_relat_1(X77)
      | ~ r1_tarski(X78,X79)
      | k9_relat_1(k7_relat_1(X77,X79),X78) = k9_relat_1(X77,X78) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_4,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_tarski(esk3_0,esk2_0)
    & k9_relat_1(esk1_0,esk3_0) != k9_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k9_relat_1(k7_relat_1(X1,esk2_0),esk3_0) = k9_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,negated_conjecture,
    ( k9_relat_1(esk1_0,esk3_0) != k9_relat_1(k7_relat_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_10,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),
    [proof]).
%------------------------------------------------------------------------------
