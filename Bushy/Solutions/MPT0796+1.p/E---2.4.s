%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t48_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   19 (  26 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   54 (  67 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r4_wellord1(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t48_wellord1.p',t48_wellord1)).

fof(t47_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t48_wellord1.p',t47_wellord1)).

fof(d8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
          <=> ? [X3] :
                ( v1_relat_1(X3)
                & v1_funct_1(X3)
                & r3_wellord1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t48_wellord1.p',d8_wellord1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t48_wellord1.p',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t48_wellord1.p',dt_k6_relat_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => r4_wellord1(X1,X1) ) ),
    inference(assume_negation,[status(cth)],[t48_wellord1])).

fof(c_0_6,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | r3_wellord1(X13,X13,k6_relat_1(k3_relat_1(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_wellord1])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ~ r4_wellord1(esk1_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X7,X8,X10] :
      ( ( v1_relat_1(esk2_2(X7,X8))
        | ~ r4_wellord1(X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( v1_funct_1(esk2_2(X7,X8))
        | ~ r4_wellord1(X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r3_wellord1(X7,X8,esk2_2(X7,X8))
        | ~ r4_wellord1(X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ r3_wellord1(X7,X8,X10)
        | r4_wellord1(X7,X8)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

cnf(c_0_9,plain,
    ( r3_wellord1(X1,X1,k6_relat_1(k3_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X14] :
      ( v1_relat_1(k6_relat_1(X14))
      & v1_funct_1(k6_relat_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_12,plain,(
    ! [X11] : v1_relat_1(k6_relat_1(X11)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_13,plain,
    ( r4_wellord1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r3_wellord1(esk1_0,esk1_0,k6_relat_1(k3_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( ~ r4_wellord1(esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_10]),c_0_16])]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
