%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord2__t12_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:16 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   31 (  56 expanded)
%              Number of clauses        :   20 (  23 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   94 ( 209 expanded)
%              Number of equality atoms :    8 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X2,X3) )
               => r4_wellord1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t12_wellord2.p',t52_wellord1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t12_wellord2.p',dt_k1_wellord2)).

fof(t12_wellord2,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ! [X3] :
              ( v3_ordinal1(X3)
             => ( ( r4_wellord1(X1,k1_wellord2(X2))
                  & r4_wellord1(X1,k1_wellord2(X3)) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t12_wellord2.p',t12_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t12_wellord2.p',t50_wellord1)).

fof(t11_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t12_wellord2.p',t11_wellord2)).

fof(c_0_5,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | ~ r4_wellord1(X12,X13)
      | ~ r4_wellord1(X13,X14)
      | r4_wellord1(X12,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).

fof(c_0_6,plain,(
    ! [X7] : v1_relat_1(k1_wellord2(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ! [X3] :
                ( v3_ordinal1(X3)
               => ( ( r4_wellord1(X1,k1_wellord2(X2))
                    & r4_wellord1(X1,k1_wellord2(X3)) )
                 => X2 = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_wellord2])).

cnf(c_0_8,plain,
    ( r4_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & r4_wellord1(esk1_0,k1_wellord2(esk2_0))
    & r4_wellord1(esk1_0,k1_wellord2(esk3_0))
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | ~ r4_wellord1(X10,X11)
      | r4_wellord1(X11,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_12,plain,
    ( r4_wellord1(X1,k1_wellord2(X2))
    | ~ r4_wellord1(X3,k1_wellord2(X2))
    | ~ r4_wellord1(X1,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X8,X9] :
      ( ~ v3_ordinal1(X8)
      | ~ v3_ordinal1(X9)
      | ~ r4_wellord1(k1_wellord2(X8),k1_wellord2(X9))
      | X8 = X9 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_wellord2])])])).

cnf(c_0_16,negated_conjecture,
    ( r4_wellord1(X1,k1_wellord2(X2))
    | ~ r4_wellord1(esk1_0,k1_wellord2(X2))
    | ~ r4_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r4_wellord1(k1_wellord2(X1),X2)
    | ~ r4_wellord1(X2,k1_wellord2(X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
    | ~ r4_wellord1(esk1_0,k1_wellord2(X2))
    | ~ r4_wellord1(k1_wellord2(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( r4_wellord1(esk1_0,k1_wellord2(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r4_wellord1(k1_wellord2(X1),esk1_0)
    | ~ r4_wellord1(esk1_0,k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r4_wellord1(esk1_0,k1_wellord2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( X1 = esk3_0
    | ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(esk3_0))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( r4_wellord1(k1_wellord2(X1),k1_wellord2(esk3_0))
    | ~ r4_wellord1(k1_wellord2(X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
