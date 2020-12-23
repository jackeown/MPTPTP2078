%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t65_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:15 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   19 (  35 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   86 ( 194 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r4_wellord1(X1,X2)
              & v2_wellord1(X1) )
           => v2_wellord1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t65_wellord1.p',t65_wellord1)).

fof(t54_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( v2_wellord1(X1)
                  & r3_wellord1(X1,X2,X3) )
               => v2_wellord1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t65_wellord1.p',t54_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/wellord1__t65_wellord1.p',d8_wellord1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r4_wellord1(X1,X2)
                & v2_wellord1(X1) )
             => v2_wellord1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_wellord1])).

fof(c_0_4,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v2_wellord1(X10)
      | ~ r3_wellord1(X10,X11,X12)
      | v2_wellord1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_wellord1])])])).

fof(c_0_5,plain,(
    ! [X6,X7,X9] :
      ( ( v1_relat_1(esk3_2(X6,X7))
        | ~ r4_wellord1(X6,X7)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( v1_funct_1(esk3_2(X6,X7))
        | ~ r4_wellord1(X6,X7)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( r3_wellord1(X6,X7,esk3_2(X6,X7))
        | ~ r4_wellord1(X6,X7)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) )
      & ( ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9)
        | ~ r3_wellord1(X6,X7,X9)
        | r4_wellord1(X6,X7)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & r4_wellord1(esk1_0,esk2_0)
    & v2_wellord1(esk1_0)
    & ~ v2_wellord1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( v2_wellord1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v2_wellord1(X1)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r3_wellord1(X1,X2,esk3_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(esk3_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_funct_1(esk3_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v2_wellord1(X1)
    | ~ v2_wellord1(X2)
    | ~ r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_wellord1(X1)
    | ~ r4_wellord1(X1,esk2_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_15,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( r4_wellord1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
