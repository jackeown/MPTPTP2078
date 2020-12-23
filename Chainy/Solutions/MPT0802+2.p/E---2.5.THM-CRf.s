%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0802+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:52 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 229 expanded)
%              Number of clauses        :   33 (  71 expanded)
%              Number of leaves         :    4 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  183 (1453 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => ( ( v1_relat_2(X1)
                   => v1_relat_2(X2) )
                  & ( v8_relat_2(X1)
                   => v8_relat_2(X2) )
                  & ( v6_relat_2(X1)
                   => v6_relat_2(X2) )
                  & ( v4_relat_2(X1)
                   => v4_relat_2(X2) )
                  & ( v1_wellord1(X1)
                   => v1_wellord1(X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_wellord1)).

fof(t54_wellord1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(c_0_3,plain,(
    ! [X1,X2] :
      ( epred2_2(X2,X1)
    <=> ( ( v1_relat_2(X1)
         => v1_relat_2(X2) )
        & ( v8_relat_2(X1)
         => v8_relat_2(X2) )
        & ( v6_relat_2(X1)
         => v6_relat_2(X2) )
        & ( v4_relat_2(X1)
         => v4_relat_2(X2) )
        & ( v1_wellord1(X1)
         => v1_wellord1(X2) ) ) ) ),
    introduced(definition)).

fof(c_0_4,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => epred2_2(X2,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t53_wellord1,c_0_3])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( v2_wellord1(X1)
                    & r3_wellord1(X1,X2,X3) )
                 => v2_wellord1(X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_wellord1])).

fof(c_0_6,plain,(
    ! [X1,X2] :
      ( epred2_2(X2,X1)
     => ( ( v1_relat_2(X1)
         => v1_relat_2(X2) )
        & ( v8_relat_2(X1)
         => v8_relat_2(X2) )
        & ( v6_relat_2(X1)
         => v6_relat_2(X2) )
        & ( v4_relat_2(X1)
         => v4_relat_2(X2) )
        & ( v1_wellord1(X1)
         => v1_wellord1(X2) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_3])).

fof(c_0_7,plain,(
    ! [X3535,X3536,X3537] :
      ( ~ v1_relat_1(X3535)
      | ~ v1_relat_1(X3536)
      | ~ v1_relat_1(X3537)
      | ~ v1_funct_1(X3537)
      | ~ r3_wellord1(X3535,X3536,X3537)
      | epred2_2(X3536,X3535) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk288_0)
    & v1_relat_1(esk289_0)
    & v1_relat_1(esk290_0)
    & v1_funct_1(esk290_0)
    & v2_wellord1(esk288_0)
    & r3_wellord1(esk288_0,esk289_0,esk290_0)
    & ~ v2_wellord1(esk289_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X3357] :
      ( ( v1_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v8_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v4_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v6_relat_2(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( v1_wellord1(X3357)
        | ~ v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) )
      & ( ~ v1_relat_2(X3357)
        | ~ v8_relat_2(X3357)
        | ~ v4_relat_2(X3357)
        | ~ v6_relat_2(X3357)
        | ~ v1_wellord1(X3357)
        | v2_wellord1(X3357)
        | ~ v1_relat_1(X3357) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

fof(c_0_10,plain,(
    ! [X3554,X3555] :
      ( ( ~ v1_relat_2(X3554)
        | v1_relat_2(X3555)
        | ~ epred2_2(X3555,X3554) )
      & ( ~ v8_relat_2(X3554)
        | v8_relat_2(X3555)
        | ~ epred2_2(X3555,X3554) )
      & ( ~ v6_relat_2(X3554)
        | v6_relat_2(X3555)
        | ~ epred2_2(X3555,X3554) )
      & ( ~ v4_relat_2(X3554)
        | v4_relat_2(X3555)
        | ~ epred2_2(X3555,X3554) )
      & ( ~ v1_wellord1(X3554)
        | v1_wellord1(X3555)
        | ~ epred2_2(X3555,X3554) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( epred2_2(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( r3_wellord1(esk288_0,esk289_0,esk290_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk290_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk290_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk289_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk288_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( v2_wellord1(esk288_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_wellord1(esk289_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( v4_relat_2(X2)
    | ~ v4_relat_2(X1)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( epred2_2(esk289_0,esk288_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_25,negated_conjecture,
    ( v4_relat_2(esk288_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_18])])).

cnf(c_0_26,plain,
    ( v8_relat_2(X2)
    | ~ v8_relat_2(X1)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( v8_relat_2(esk288_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_18])])).

cnf(c_0_28,plain,
    ( v6_relat_2(X2)
    | ~ v6_relat_2(X1)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( v6_relat_2(esk288_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_18])])).

cnf(c_0_30,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_2(esk289_0)
    | ~ v1_wellord1(esk289_0)
    | ~ v8_relat_2(esk289_0)
    | ~ v6_relat_2(esk289_0)
    | ~ v4_relat_2(esk289_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_22])).

cnf(c_0_32,plain,
    ( v4_relat_2(esk289_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_33,plain,
    ( v8_relat_2(esk289_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_27])])).

cnf(c_0_34,plain,
    ( v6_relat_2(esk289_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_29])])).

cnf(c_0_35,plain,
    ( v1_wellord1(X2)
    | ~ v1_wellord1(X1)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,negated_conjecture,
    ( v1_wellord1(esk288_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_16]),c_0_18])])).

cnf(c_0_37,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_relat_2(esk289_0)
    | ~ v1_wellord1(esk289_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),c_0_33]),c_0_34])])).

cnf(c_0_39,plain,
    ( v1_wellord1(esk289_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_36])])).

cnf(c_0_40,plain,
    ( v1_relat_2(X2)
    | ~ v1_relat_2(X1)
    | ~ epred2_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_2(esk288_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_18])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_relat_2(esk289_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_43,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_24]),c_0_41])]),c_0_42]),
    [proof]).
%------------------------------------------------------------------------------
