%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:53 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 136 expanded)
%              Number of clauses        :   23 (  41 expanded)
%              Number of leaves         :    4 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  131 (1162 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v10_lattices(X3)
                & l3_lattices(X3) )
             => ( ( r1_filter_1(X1,X2)
                  & r1_filter_1(X2,X3) )
               => r1_filter_1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_filter_1)).

fof(d9_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v10_lattices(X2)
            & l3_lattices(X2) )
         => ( r1_filter_1(X1,X2)
          <=> r4_wellord1(k8_filter_1(X1),k8_filter_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_filter_1)).

fof(dt_k8_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => v1_relat_1(k8_filter_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_filter_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v10_lattices(X2)
              & l3_lattices(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v10_lattices(X3)
                  & l3_lattices(X3) )
               => ( ( r1_filter_1(X1,X2)
                    & r1_filter_1(X2,X3) )
                 => r1_filter_1(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_filter_1])).

fof(c_0_5,plain,(
    ! [X7,X8] :
      ( ( ~ r1_filter_1(X7,X8)
        | r4_wellord1(k8_filter_1(X7),k8_filter_1(X8))
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) )
      & ( ~ r4_wellord1(k8_filter_1(X7),k8_filter_1(X8))
        | r1_filter_1(X7,X8)
        | v2_struct_0(X8)
        | ~ v10_lattices(X8)
        | ~ l3_lattices(X8)
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_filter_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v10_lattices(esk3_0)
    & l3_lattices(esk3_0)
    & r1_filter_1(esk1_0,esk2_0)
    & r1_filter_1(esk2_0,esk3_0)
    & ~ r1_filter_1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ v10_lattices(X9)
      | ~ l3_lattices(X9)
      | v1_relat_1(k8_filter_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_filter_1])])])).

fof(c_0_8,plain,(
    ! [X4,X5,X6] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ r4_wellord1(X4,X5)
      | ~ r4_wellord1(X5,X6)
      | r4_wellord1(X4,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).

cnf(c_0_9,plain,
    ( r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_filter_1(X1,X2)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( r1_filter_1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | v1_relat_1(k8_filter_1(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r4_wellord1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r4_wellord1(X1,X2)
    | ~ r4_wellord1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( r4_wellord1(k8_filter_1(esk2_0),k8_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(k8_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_11]),c_0_13])]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k8_filter_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_12]),c_0_14])]),c_0_16])).

cnf(c_0_22,plain,
    ( r1_filter_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r4_wellord1(X1,k8_filter_1(esk3_0))
    | ~ r4_wellord1(X1,k8_filter_1(esk2_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_24,negated_conjecture,
    ( r1_filter_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( r1_filter_1(X1,esk3_0)
    | v2_struct_0(X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ r4_wellord1(k8_filter_1(X1),k8_filter_1(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_11]),c_0_13])]),c_0_15]),c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( r4_wellord1(k8_filter_1(esk1_0),k8_filter_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_24]),c_0_12]),c_0_25]),c_0_14]),c_0_26])]),c_0_16]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_filter_1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_25]),c_0_26])]),c_0_30]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:44:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t34_filter_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>![X3]:(((~(v2_struct_0(X3))&v10_lattices(X3))&l3_lattices(X3))=>((r1_filter_1(X1,X2)&r1_filter_1(X2,X3))=>r1_filter_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_filter_1)).
% 0.19/0.37  fof(d9_filter_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>(r1_filter_1(X1,X2)<=>r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_filter_1)).
% 0.19/0.37  fof(dt_k8_filter_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>v1_relat_1(k8_filter_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_filter_1)).
% 0.19/0.37  fof(t52_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r4_wellord1(X1,X2)&r4_wellord1(X2,X3))=>r4_wellord1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_wellord1)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>![X3]:(((~(v2_struct_0(X3))&v10_lattices(X3))&l3_lattices(X3))=>((r1_filter_1(X1,X2)&r1_filter_1(X2,X3))=>r1_filter_1(X1,X3)))))), inference(assume_negation,[status(cth)],[t34_filter_1])).
% 0.19/0.37  fof(c_0_5, plain, ![X7, X8]:((~r1_filter_1(X7,X8)|r4_wellord1(k8_filter_1(X7),k8_filter_1(X8))|(v2_struct_0(X8)|~v10_lattices(X8)|~l3_lattices(X8))|(v2_struct_0(X7)|~v10_lattices(X7)|~l3_lattices(X7)))&(~r4_wellord1(k8_filter_1(X7),k8_filter_1(X8))|r1_filter_1(X7,X8)|(v2_struct_0(X8)|~v10_lattices(X8)|~l3_lattices(X8))|(v2_struct_0(X7)|~v10_lattices(X7)|~l3_lattices(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_filter_1])])])])])).
% 0.19/0.37  fof(c_0_6, negated_conjecture, (((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&l3_lattices(esk1_0))&(((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&l3_lattices(esk2_0))&(((~v2_struct_0(esk3_0)&v10_lattices(esk3_0))&l3_lattices(esk3_0))&((r1_filter_1(esk1_0,esk2_0)&r1_filter_1(esk2_0,esk3_0))&~r1_filter_1(esk1_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.19/0.37  fof(c_0_7, plain, ![X9]:(v2_struct_0(X9)|~v10_lattices(X9)|~l3_lattices(X9)|v1_relat_1(k8_filter_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_filter_1])])])).
% 0.19/0.37  fof(c_0_8, plain, ![X4, X5, X6]:(~v1_relat_1(X4)|(~v1_relat_1(X5)|(~v1_relat_1(X6)|(~r4_wellord1(X4,X5)|~r4_wellord1(X5,X6)|r4_wellord1(X4,X6))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t52_wellord1])])])).
% 0.19/0.37  cnf(c_0_9, plain, (r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))|v2_struct_0(X2)|v2_struct_0(X1)|~r1_filter_1(X1,X2)|~v10_lattices(X2)|~l3_lattices(X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (r1_filter_1(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (l3_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (v10_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_17, plain, (v2_struct_0(X1)|v1_relat_1(k8_filter_1(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_18, plain, (r4_wellord1(X1,X3)|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r4_wellord1(X1,X2)|~r4_wellord1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (r4_wellord1(k8_filter_1(esk2_0),k8_filter_1(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15]), c_0_16])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (v1_relat_1(k8_filter_1(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_11]), c_0_13])]), c_0_15])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (v1_relat_1(k8_filter_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_12]), c_0_14])]), c_0_16])).
% 0.19/0.37  cnf(c_0_22, plain, (r1_filter_1(X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~r4_wellord1(k8_filter_1(X1),k8_filter_1(X2))|~v10_lattices(X2)|~l3_lattices(X2)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r4_wellord1(X1,k8_filter_1(esk3_0))|~r4_wellord1(X1,k8_filter_1(esk2_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (r1_filter_1(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (r1_filter_1(X1,esk3_0)|v2_struct_0(X1)|~l3_lattices(X1)|~v10_lattices(X1)|~r4_wellord1(k8_filter_1(X1),k8_filter_1(esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_11]), c_0_13])]), c_0_15]), c_0_17])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r4_wellord1(k8_filter_1(esk1_0),k8_filter_1(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_24]), c_0_12]), c_0_25]), c_0_14]), c_0_26])]), c_0_16]), c_0_27])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (~r1_filter_1(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_25]), c_0_26])]), c_0_30]), c_0_27]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 32
% 0.19/0.37  # Proof object clause steps            : 23
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 22
% 0.19/0.37  # Proof object clause conjectures      : 19
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 16
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 7
% 0.19/0.37  # Proof object simplifying inferences  : 33
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 42
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 42
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 13
% 0.19/0.37  # ...of the previous two non-trivial   : 10
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 13
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 26
% 0.19/0.37  #    Positive orientable unit clauses  : 13
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 9
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 16
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 27
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 7
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 12
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 0
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1502
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.030 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
