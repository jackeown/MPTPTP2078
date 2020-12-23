%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0798+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   27 ( 148 expanded)
%              Number of clauses        :   18 (  48 expanded)
%              Number of leaves         :    4 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 619 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
           => r4_wellord1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).

fof(t49_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => r3_wellord1(X2,X1,k2_funct_1(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_wellord1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT008+2.ax',dt_k2_funct_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r4_wellord1(X1,X2)
             => r4_wellord1(X2,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_wellord1])).

fof(c_0_5,plain,(
    ! [X3378,X3379,X3381] :
      ( ( v1_relat_1(esk265_2(X3378,X3379))
        | ~ r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) )
      & ( v1_funct_1(esk265_2(X3378,X3379))
        | ~ r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) )
      & ( r3_wellord1(X3378,X3379,esk265_2(X3378,X3379))
        | ~ r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) )
      & ( ~ v1_relat_1(X3381)
        | ~ v1_funct_1(X3381)
        | ~ r3_wellord1(X3378,X3379,X3381)
        | r4_wellord1(X3378,X3379)
        | ~ v1_relat_1(X3379)
        | ~ v1_relat_1(X3378) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk288_0)
    & v1_relat_1(esk289_0)
    & r4_wellord1(esk288_0,esk289_0)
    & ~ r4_wellord1(esk289_0,esk288_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X3522,X3523,X3524] :
      ( ~ v1_relat_1(X3522)
      | ~ v1_relat_1(X3523)
      | ~ v1_relat_1(X3524)
      | ~ v1_funct_1(X3524)
      | ~ r3_wellord1(X3522,X3523,X3524)
      | r3_wellord1(X3523,X3522,k2_funct_1(X3524)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_wellord1])])])).

cnf(c_0_8,plain,
    ( r3_wellord1(X1,X2,esk265_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r4_wellord1(esk288_0,esk289_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_relat_1(esk289_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk288_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( v1_funct_1(esk265_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,plain,
    ( v1_relat_1(esk265_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_14,plain,(
    ! [X2777] :
      ( ( v1_relat_1(k2_funct_1(X2777))
        | ~ v1_relat_1(X2777)
        | ~ v1_funct_1(X2777) )
      & ( v1_funct_1(k2_funct_1(X2777))
        | ~ v1_relat_1(X2777)
        | ~ v1_funct_1(X2777) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_15,plain,
    ( r3_wellord1(X2,X1,k2_funct_1(X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( r3_wellord1(esk288_0,esk289_0,esk265_2(esk288_0,esk289_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk265_2(esk288_0,esk289_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk265_2(esk288_0,esk289_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_19,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r4_wellord1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( r3_wellord1(esk289_0,esk288_0,k2_funct_1(esk265_2(esk288_0,esk289_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_10]),c_0_11])])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk265_2(esk288_0,esk289_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk265_2(esk288_0,esk289_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_18])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r4_wellord1(esk289_0,esk288_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_11]),c_0_10]),c_0_24])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
