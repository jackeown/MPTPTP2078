%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  89 expanded)
%              Number of clauses        :   29 (  31 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :  223 ( 667 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    2 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(t65_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r4_wellord1(X1,X2)
              & v2_wellord1(X1) )
           => v2_wellord1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).

fof(c_0_4,plain,(
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

fof(c_0_5,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_4])).

fof(c_0_6,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( r3_wellord1(X1,X2,X3)
               => epred1_2(X2,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t53_wellord1,c_0_4])).

fof(c_0_7,plain,(
    ! [X14,X15] :
      ( ( ~ v1_relat_2(X14)
        | v1_relat_2(X15)
        | ~ epred1_2(X15,X14) )
      & ( ~ v8_relat_2(X14)
        | v8_relat_2(X15)
        | ~ epred1_2(X15,X14) )
      & ( ~ v6_relat_2(X14)
        | v6_relat_2(X15)
        | ~ epred1_2(X15,X14) )
      & ( ~ v4_relat_2(X14)
        | v4_relat_2(X15)
        | ~ epred1_2(X15,X14) )
      & ( ~ v1_wellord1(X14)
        | v1_wellord1(X15)
        | ~ epred1_2(X15,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
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

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ r3_wellord1(X9,X10,X11)
      | epred1_2(X10,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X5,X6,X8] :
      ( ( v1_relat_1(esk1_2(X5,X6))
        | ~ r4_wellord1(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( v1_funct_1(esk1_2(X5,X6))
        | ~ r4_wellord1(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( r3_wellord1(X5,X6,esk1_2(X5,X6))
        | ~ r4_wellord1(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ r3_wellord1(X5,X6,X8)
        | r4_wellord1(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r4_wellord1(X1,X2)
                & v2_wellord1(X1) )
             => v2_wellord1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_wellord1])).

cnf(c_0_12,plain,
    ( v1_wellord1(X2)
    | ~ v1_wellord1(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_wellord1(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_relat_2(X2)
    | ~ v1_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v8_relat_2(X2)
    | ~ v8_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v8_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( v4_relat_2(X2)
    | ~ v4_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( v4_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( v6_relat_2(X2)
    | ~ v6_relat_2(X1)
    | ~ epred1_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( v6_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( epred1_2(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ r3_wellord1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( r3_wellord1(X1,X2,esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( v1_funct_1(esk1_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r4_wellord1(esk2_0,esk3_0)
    & v2_wellord1(esk2_0)
    & ~ v2_wellord1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_27,plain,
    ( v2_wellord1(X1)
    | ~ v1_relat_2(X1)
    | ~ v8_relat_2(X1)
    | ~ v4_relat_2(X1)
    | ~ v6_relat_2(X1)
    | ~ v1_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( v1_wellord1(X1)
    | ~ epred1_2(X1,X2)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_29,plain,
    ( v1_relat_2(X1)
    | ~ epred1_2(X1,X2)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_30,plain,
    ( v8_relat_2(X1)
    | ~ epred1_2(X1,X2)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_31,plain,
    ( v4_relat_2(X1)
    | ~ epred1_2(X1,X2)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_32,plain,
    ( v6_relat_2(X1)
    | ~ epred1_2(X1,X2)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( epred1_2(X1,X2)
    | ~ r4_wellord1(X2,X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r4_wellord1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v2_wellord1(X1)
    | ~ epred1_2(X1,X2)
    | ~ v2_wellord1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( epred1_2(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( v2_wellord1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_wellord1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_35]),c_0_36])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:28:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02FN
% 0.20/0.38  # and selection function PSelectNonAntiRROptimalLit.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t53_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_wellord1)).
% 0.20/0.38  fof(d4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v2_wellord1(X1)<=>((((v1_relat_2(X1)&v8_relat_2(X1))&v4_relat_2(X1))&v6_relat_2(X1))&v1_wellord1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 0.20/0.38  fof(d8_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r4_wellord1(X1,X2)<=>?[X3]:((v1_relat_1(X3)&v1_funct_1(X3))&r3_wellord1(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_wellord1)).
% 0.20/0.38  fof(t65_wellord1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((r4_wellord1(X1,X2)&v2_wellord1(X1))=>v2_wellord1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_wellord1)).
% 0.20/0.38  fof(c_0_4, plain, ![X1, X2]:(epred1_2(X2,X1)<=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2)))), introduced(definition)).
% 0.20/0.38  fof(c_0_5, plain, ![X1, X2]:(epred1_2(X2,X1)=>(((((v1_relat_2(X1)=>v1_relat_2(X2))&(v8_relat_2(X1)=>v8_relat_2(X2)))&(v6_relat_2(X1)=>v6_relat_2(X2)))&(v4_relat_2(X1)=>v4_relat_2(X2)))&(v1_wellord1(X1)=>v1_wellord1(X2)))), inference(split_equiv,[status(thm)],[c_0_4])).
% 0.20/0.38  fof(c_0_6, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r3_wellord1(X1,X2,X3)=>epred1_2(X2,X1))))), inference(apply_def,[status(thm)],[t53_wellord1, c_0_4])).
% 0.20/0.38  fof(c_0_7, plain, ![X14, X15]:(((((~v1_relat_2(X14)|v1_relat_2(X15)|~epred1_2(X15,X14))&(~v8_relat_2(X14)|v8_relat_2(X15)|~epred1_2(X15,X14)))&(~v6_relat_2(X14)|v6_relat_2(X15)|~epred1_2(X15,X14)))&(~v4_relat_2(X14)|v4_relat_2(X15)|~epred1_2(X15,X14)))&(~v1_wellord1(X14)|v1_wellord1(X15)|~epred1_2(X15,X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X4]:((((((v1_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4))&(v8_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(v4_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(v6_relat_2(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(v1_wellord1(X4)|~v2_wellord1(X4)|~v1_relat_1(X4)))&(~v1_relat_2(X4)|~v8_relat_2(X4)|~v4_relat_2(X4)|~v6_relat_2(X4)|~v1_wellord1(X4)|v2_wellord1(X4)|~v1_relat_1(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X9, X10, X11]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11)|(~r3_wellord1(X9,X10,X11)|epred1_2(X10,X9))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.20/0.38  fof(c_0_10, plain, ![X5, X6, X8]:((((v1_relat_1(esk1_2(X5,X6))|~r4_wellord1(X5,X6)|~v1_relat_1(X6)|~v1_relat_1(X5))&(v1_funct_1(esk1_2(X5,X6))|~r4_wellord1(X5,X6)|~v1_relat_1(X6)|~v1_relat_1(X5)))&(r3_wellord1(X5,X6,esk1_2(X5,X6))|~r4_wellord1(X5,X6)|~v1_relat_1(X6)|~v1_relat_1(X5)))&(~v1_relat_1(X8)|~v1_funct_1(X8)|~r3_wellord1(X5,X6,X8)|r4_wellord1(X5,X6)|~v1_relat_1(X6)|~v1_relat_1(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>((r4_wellord1(X1,X2)&v2_wellord1(X1))=>v2_wellord1(X2))))), inference(assume_negation,[status(cth)],[t65_wellord1])).
% 0.20/0.38  cnf(c_0_12, plain, (v1_wellord1(X2)|~v1_wellord1(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_13, plain, (v1_wellord1(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, plain, (v1_relat_2(X2)|~v1_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_15, plain, (v1_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_16, plain, (v8_relat_2(X2)|~v8_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_17, plain, (v8_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_18, plain, (v4_relat_2(X2)|~v4_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_19, plain, (v4_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_20, plain, (v6_relat_2(X2)|~v6_relat_2(X1)|~epred1_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_21, plain, (v6_relat_2(X1)|~v2_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_22, plain, (epred1_2(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)|~r3_wellord1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_23, plain, (r3_wellord1(X1,X2,esk1_2(X1,X2))|~r4_wellord1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_24, plain, (v1_relat_1(esk1_2(X1,X2))|~r4_wellord1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_25, plain, (v1_funct_1(esk1_2(X1,X2))|~r4_wellord1(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_26, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&((r4_wellord1(esk2_0,esk3_0)&v2_wellord1(esk2_0))&~v2_wellord1(esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.38  cnf(c_0_27, plain, (v2_wellord1(X1)|~v1_relat_2(X1)|~v8_relat_2(X1)|~v4_relat_2(X1)|~v6_relat_2(X1)|~v1_wellord1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_28, plain, (v1_wellord1(X1)|~epred1_2(X1,X2)|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.38  cnf(c_0_29, plain, (v1_relat_2(X1)|~epred1_2(X1,X2)|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.38  cnf(c_0_30, plain, (v8_relat_2(X1)|~epred1_2(X1,X2)|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.38  cnf(c_0_31, plain, (v4_relat_2(X1)|~epred1_2(X1,X2)|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.38  cnf(c_0_32, plain, (v6_relat_2(X1)|~epred1_2(X1,X2)|~v2_wellord1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.38  cnf(c_0_33, plain, (epred1_2(X1,X2)|~r4_wellord1(X2,X1)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r4_wellord1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_37, plain, (v2_wellord1(X1)|~epred1_2(X1,X2)|~v2_wellord1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (epred1_2(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (v2_wellord1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (~v2_wellord1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_35]), c_0_36])]), c_0_40]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 42
% 0.20/0.38  # Proof object clause steps            : 29
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 10
% 0.20/0.38  # Proof object clause conjectures      : 7
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 4
% 0.20/0.38  # Proof object generating inferences   : 9
% 0.20/0.38  # Proof object simplifying inferences  : 14
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 4
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 21
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 21
% 0.20/0.38  # Processed clauses                    : 69
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 6
% 0.20/0.38  # ...remaining for further processing  : 63
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 0
% 0.20/0.38  # Generated clauses                    : 85
% 0.20/0.38  # ...of the previous two non-trivial   : 81
% 0.20/0.38  # Contextual simplify-reflections      : 6
% 0.20/0.38  # Paramodulations                      : 85
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 0
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 42
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 1
% 0.20/0.38  #    Non-unit-clauses                  : 36
% 0.20/0.38  # Current number of unprocessed clauses: 54
% 0.20/0.38  # ...number of literals in the above   : 378
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 21
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 238
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 116
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 0
% 0.20/0.38  # BW rewrite match successes           : 0
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2882
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.033 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.037 s
% 0.20/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
