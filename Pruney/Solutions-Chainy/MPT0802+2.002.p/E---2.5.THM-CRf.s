%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:59 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 227 expanded)
%              Number of clauses        :   31 (  69 expanded)
%              Number of leaves         :    4 (  58 expanded)
%              Depth                    :    7
%              Number of atoms          :  181 (1451 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
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
      ( epred1_2(X2,X1)
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
               => epred1_2(X2,X1) ) ) ) ) ),
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
      ( epred1_2(X2,X1)
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
    ! [X5,X6,X7] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ r3_wellord1(X5,X6,X7)
      | epred1_2(X6,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & v2_wellord1(esk1_0)
    & r3_wellord1(esk1_0,esk2_0,esk3_0)
    & ~ v2_wellord1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ( ~ v1_relat_2(X11)
        | v1_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v8_relat_2(X11)
        | v8_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v6_relat_2(X11)
        | v6_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v4_relat_2(X11)
        | v4_relat_2(X12)
        | ~ epred1_2(X12,X11) )
      & ( ~ v1_wellord1(X11)
        | v1_wellord1(X12)
        | ~ epred1_2(X12,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_10,plain,
    ( epred1_2(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r3_wellord1(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v1_wellord1(X2)
    | ~ v1_wellord1(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( epred1_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

fof(c_0_18,plain,(
    ! [X4] :
      ( ( v1_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v8_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v4_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v6_relat_2(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( v1_wellord1(X4)
        | ~ v2_wellord1(X4)
        | ~ v1_relat_1(X4) )
      & ( ~ v1_relat_2(X4)
        | ~ v8_relat_2(X4)
        | ~ v4_relat_2(X4)
        | ~ v6_relat_2(X4)
        | ~ v1_wellord1(X4)
        | v2_wellord1(X4)
        | ~ v1_relat_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_19,plain,
    ( v6_relat_2(X2)
    | ~ v6_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( v4_relat_2(X2)
    | ~ v4_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( v8_relat_2(X2)
    | ~ v8_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( v1_relat_2(X2)
    | ~ v1_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( v1_wellord1(esk2_0)
    | ~ v1_wellord1(esk1_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v2_wellord1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( v6_relat_2(esk2_0)
    | ~ v6_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_27,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( v4_relat_2(esk2_0)
    | ~ v4_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_29,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,plain,
    ( v8_relat_2(esk2_0)
    | ~ v8_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_17])).

cnf(c_0_31,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( v1_relat_2(esk2_0)
    | ~ v1_relat_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_33,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,plain,
    ( v1_wellord1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_15])])).

cnf(c_0_36,plain,
    ( v6_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_25]),c_0_15])])).

cnf(c_0_37,plain,
    ( v4_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_15])])).

cnf(c_0_38,plain,
    ( v8_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25]),c_0_15])])).

cnf(c_0_39,plain,
    ( v1_relat_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_15])])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_14])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___008_C45_F1_PI_AE_Q4_CS_SP_S4S
% 0.13/0.37  # and selection function SelectNewComplexAHPNS.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t53_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_wellord1)).
% 0.13/0.37  fof(t54_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((v2_wellord1(X1)&r3_wellord1(X1,X2,X3))=>v2_wellord1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_wellord1)).
% 0.13/0.37  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 0.13/0.37  fof(c_0_3, plain, ![X1, X2]:(epred1_2(X2,X1)<=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2)))), introduced(definition)).
% 0.13/0.37  fof(c_0_4, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>epred1_2(X2,X1))))), inference(apply_def,[status(thm)],[t53_wellord1, c_0_3])).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((v2_wellord1(X1)&r3_wellord1(X1,X2,X3))=>v2_wellord1(X2)))))), inference(assume_negation,[status(cth)],[t54_wellord1])).
% 0.13/0.37  fof(c_0_6, plain, ![X1, X2]:(epred1_2(X2,X1)=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2)))), inference(split_equiv,[status(thm)],[c_0_3])).
% 0.13/0.37  fof(c_0_7, plain, ![X5, X6, X7]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7)|(~r3_wellord1(X5,X6,X7)|epred1_2(X6,X5))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.13/0.37  fof(c_0_8, negated_conjecture, (v1_relat_1(esk1_0)&(v1_relat_1(esk2_0)&((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((v2_wellord1(esk1_0)&r3_wellord1(esk1_0,esk2_0,esk3_0))&~v2_wellord1(esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.37  fof(c_0_9, plain, ![X11, X12]:(((((~v1_relat_2(X11)|v1_relat_2(X12)|~epred1_2(X12,X11))&(~v8_relat_2(X11)|v8_relat_2(X12)|~epred1_2(X12,X11)))&(~v6_relat_2(X11)|v6_relat_2(X12)|~epred1_2(X12,X11)))&(~v4_relat_2(X11)|v4_relat_2(X12)|~epred1_2(X12,X11)))&(~v1_wellord1(X11)|v1_wellord1(X12)|~epred1_2(X12,X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.37  cnf(c_0_10, plain, (epred1_2(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~r3_wellord1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (r3_wellord1(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_16, plain, (v1_wellord1(X2)|~v1_wellord1(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (epred1_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15])])).
% 0.13/0.37  fof(c_0_18, plain, ![X4]:((((((v1_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4))&(v8_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(v4_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(v6_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(v1_wellord1(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(~v1_relat_2(X4)|~v8_relat_2(X4)|~v4_relat_2(X4)|~v6_relat_2(X4)|~v1_wellord1(X4)|v2_wellord1(X4)|~v1_relat_1(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.13/0.37  cnf(c_0_19, plain, (v6_relat_2(X2)|~v6_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_20, plain, (v4_relat_2(X2)|~v4_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_21, plain, (v8_relat_2(X2)|~v8_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_22, plain, (v1_relat_2(X2)|~v1_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_23, plain, (v1_wellord1(esk2_0)|~v1_wellord1(esk1_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.13/0.37  cnf(c_0_24, plain, (v1_wellord1(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (v2_wellord1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_26, plain, (v6_relat_2(esk2_0)|~v6_relat_2(esk1_0)), inference(spm,[status(thm)],[c_0_19, c_0_17])).
% 0.13/0.37  cnf(c_0_27, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_28, plain, (v4_relat_2(esk2_0)|~v4_relat_2(esk1_0)), inference(spm,[status(thm)],[c_0_20, c_0_17])).
% 0.13/0.37  cnf(c_0_29, plain, (v4_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_30, plain, (v8_relat_2(esk2_0)|~v8_relat_2(esk1_0)), inference(spm,[status(thm)],[c_0_21, c_0_17])).
% 0.13/0.37  cnf(c_0_31, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_32, plain, (v1_relat_2(esk2_0)|~v1_relat_2(esk1_0)), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.13/0.37  cnf(c_0_33, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_34, plain, (v2_wellord1(X1)|~v1_relat_2(X1)|~v8_relat_2(X1)|~v4_relat_2(X1)|~v6_relat_2(X1)|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.37  cnf(c_0_35, plain, (v1_wellord1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_15])])).
% 0.13/0.37  cnf(c_0_36, plain, (v6_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_25]), c_0_15])])).
% 0.13/0.37  cnf(c_0_37, plain, (v4_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_25]), c_0_15])])).
% 0.13/0.37  cnf(c_0_38, plain, (v8_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_25]), c_0_15])])).
% 0.13/0.37  cnf(c_0_39, plain, (v1_relat_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_15])])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (~v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_41, plain, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_14])]), c_0_40]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 42
% 0.13/0.37  # Proof object clause steps            : 31
% 0.13/0.37  # Proof object formula steps           : 11
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 19
% 0.13/0.37  # Proof object initial formulas used   : 3
% 0.13/0.37  # Proof object generating inferences   : 12
% 0.13/0.37  # Proof object simplifying inferences  : 27
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 3
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 19
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 19
% 0.13/0.37  # Processed clauses                    : 30
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 30
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 5
% 0.13/0.37  # Generated clauses                    : 13
% 0.13/0.37  # ...of the previous two non-trivial   : 11
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 13
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 25
% 0.13/0.37  #    Positive orientable unit clauses  : 12
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 12
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 5
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 5
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 0
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 5
% 0.13/0.37  # BW rewrite match successes           : 5
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1246
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.004 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
