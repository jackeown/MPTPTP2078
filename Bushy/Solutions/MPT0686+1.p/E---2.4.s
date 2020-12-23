%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t141_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   22 (  37 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 ( 102 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t141_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
         => r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t141_funct_1.p',t141_funct_1)).

fof(t137_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t141_funct_1.p',t137_funct_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t141_funct_1.p',d7_xboole_0)).

fof(t171_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t141_funct_1.p',t171_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_xboole_0(X2,X3)
           => r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t141_funct_1])).

fof(c_0_5,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | k10_relat_1(X20,k3_xboole_0(X18,X19)) = k3_xboole_0(k10_relat_1(X20,X18),k10_relat_1(X20,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & r1_xboole_0(esk2_0,esk3_0)
    & ~ r1_xboole_0(k10_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X11,X12] :
      ( ( ~ r1_xboole_0(X11,X12)
        | k3_xboole_0(X11,X12) = k1_xboole_0 )
      & ( k3_xboole_0(X11,X12) != k1_xboole_0
        | r1_xboole_0(X11,X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_8,plain,
    ( k10_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | k10_relat_1(X21,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_relat_1])])).

cnf(c_0_12,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk1_0,X1),k10_relat_1(esk1_0,X2)) = k10_relat_1(esk1_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(esk1_0,X1),k10_relat_1(esk1_0,X2))
    | k10_relat_1(esk1_0,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_xboole_0(k10_relat_1(esk1_0,esk2_0),k10_relat_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
