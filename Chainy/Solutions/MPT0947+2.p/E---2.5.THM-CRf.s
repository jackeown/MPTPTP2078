%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0947+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:58 EST 2020

% Result     : Theorem 1.45s
% Output     : CNFRefutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   25 (  50 expanded)
%              Number of clauses        :   14 (  17 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   75 ( 190 expanded)
%              Number of equality atoms :    7 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord2)).

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
    file('/export/starexec/sandbox/benchmark/Axioms/MPT010+2.ax',t52_wellord1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(t50_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT010+2.ax',t50_wellord1)).

fof(t11_wellord2,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r4_wellord1(k1_wellord2(X1),k1_wellord2(X2))
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X40)
      | ~ v1_relat_1(X41)
      | ~ v1_relat_1(X42)
      | ~ r4_wellord1(X40,X41)
      | ~ r4_wellord1(X41,X42)
      | r4_wellord1(X40,X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & r4_wellord1(esk1_0,k1_wellord2(esk2_0))
    & r4_wellord1(esk1_0,k1_wellord2(esk3_0))
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X79] : v1_relat_1(k1_wellord2(X79)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_9,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X38)
      | ~ v1_relat_1(X39)
      | ~ r4_wellord1(X38,X39)
      | r4_wellord1(X39,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_wellord1])])])).

cnf(c_0_10,plain,
    ( r4_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r4_wellord1(esk1_0,k1_wellord2(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r4_wellord1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r4_wellord1(esk1_0,k1_wellord2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_16,plain,(
    ! [X71,X72] :
      ( ~ v3_ordinal1(X71)
      | ~ v3_ordinal1(X72)
      | ~ r4_wellord1(k1_wellord2(X71),k1_wellord2(X72))
      | X71 = X72 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_wellord2])])])).

cnf(c_0_17,negated_conjecture,
    ( r4_wellord1(X1,k1_wellord2(esk3_0))
    | ~ r4_wellord1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_18,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_12]),c_0_13])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ r4_wellord1(k1_wellord2(X1),k1_wellord2(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r4_wellord1(k1_wellord2(esk2_0),k1_wellord2(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12])])).

cnf(c_0_21,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
