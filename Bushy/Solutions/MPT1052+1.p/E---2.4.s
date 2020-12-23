%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t169_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   18 (  45 expanded)
%              Number of clauses        :   13 (  21 expanded)
%              Number of leaves         :    2 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 409 expanded)
%              Number of equality atoms :   37 ( 171 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t169_funct_2.p',d2_funct_2)).

fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t169_funct_2.p',t169_funct_2)).

fof(c_0_2,plain,(
    ! [X11,X12,X13,X14,X16,X17,X18,X19,X20,X22] :
      ( ( v1_relat_1(esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k1_funct_2(X11,X12) )
      & ( v1_funct_1(esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k1_funct_2(X11,X12) )
      & ( X14 = esk4_4(X11,X12,X13,X14)
        | ~ r2_hidden(X14,X13)
        | X13 != k1_funct_2(X11,X12) )
      & ( k1_relat_1(esk4_4(X11,X12,X13,X14)) = X11
        | ~ r2_hidden(X14,X13)
        | X13 != k1_funct_2(X11,X12) )
      & ( r1_tarski(k2_relat_1(esk4_4(X11,X12,X13,X14)),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k1_funct_2(X11,X12) )
      & ( ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | X16 != X17
        | k1_relat_1(X17) != X11
        | ~ r1_tarski(k2_relat_1(X17),X12)
        | r2_hidden(X16,X13)
        | X13 != k1_funct_2(X11,X12) )
      & ( ~ r2_hidden(esk5_3(X18,X19,X20),X20)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | esk5_3(X18,X19,X20) != X22
        | k1_relat_1(X22) != X18
        | ~ r1_tarski(k2_relat_1(X22),X19)
        | X20 = k1_funct_2(X18,X19) )
      & ( v1_relat_1(esk6_3(X18,X19,X20))
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k1_funct_2(X18,X19) )
      & ( v1_funct_1(esk6_3(X18,X19,X20))
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k1_funct_2(X18,X19) )
      & ( esk5_3(X18,X19,X20) = esk6_3(X18,X19,X20)
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k1_funct_2(X18,X19) )
      & ( k1_relat_1(esk6_3(X18,X19,X20)) = X18
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k1_funct_2(X18,X19) )
      & ( r1_tarski(k2_relat_1(esk6_3(X18,X19,X20)),X19)
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k1_funct_2(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_3,plain,
    ( k1_relat_1(esk4_4(X1,X2,X3,X4)) = X1
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_4,plain,
    ( X1 = esk4_4(X2,X3,X4,X1)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_funct_2(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

cnf(c_0_6,plain,
    ( k1_relat_1(X1) = X2
    | X3 != k1_funct_2(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_3,c_0_4])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0))
    & ( k1_relat_1(esk3_0) != esk1_0
      | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_relat_1(esk4_4(X1,X2,X3,X4)),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_9,plain,
    ( k1_relat_1(X1) = X2
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk3_0,k1_funct_2(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | X3 != k1_funct_2(X4,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_8,c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( esk1_0 = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( k1_relat_1(esk3_0) != esk1_0
    | ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r2_hidden(X1,k1_funct_2(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk3_0,k1_funct_2(k1_relat_1(esk3_0),esk2_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
