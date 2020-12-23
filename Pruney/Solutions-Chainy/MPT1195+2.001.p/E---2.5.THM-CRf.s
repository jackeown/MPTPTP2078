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
% DateTime   : Thu Dec  3 11:10:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 160 expanded)
%              Number of clauses        :   22 (  52 expanded)
%              Number of leaves         :    5 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  156 (1033 expanded)
%              Number of equality atoms :   31 ( 165 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(d3_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k1_lattices(X1,X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(d8_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v8_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v8_lattices(X1)
          & v9_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_lattices(X1,X2,X3)
                <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_lattices])).

fof(c_0_6,plain,(
    ! [X4,X5,X6] :
      ( ( ~ r1_lattices(X4,X5,X6)
        | k1_lattices(X4,X5,X6) = X6
        | ~ m1_subset_1(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | v2_struct_0(X4)
        | ~ l2_lattices(X4) )
      & ( k1_lattices(X4,X5,X6) != X6
        | r1_lattices(X4,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(X4))
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | v2_struct_0(X4)
        | ~ l2_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v8_lattices(esk5_0)
    & v9_lattices(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & ( ~ r1_lattices(esk5_0,esk6_0,esk7_0)
      | k2_lattices(esk5_0,esk6_0,esk7_0) != esk6_0 )
    & ( r1_lattices(esk5_0,esk6_0,esk7_0)
      | k2_lattices(esk5_0,esk6_0,esk7_0) = esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( k1_lattices(esk5_0,X1,esk7_0) = esk7_0
    | ~ r1_lattices(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r1_lattices(esk5_0,esk6_0,esk7_0)
    | k2_lattices(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_15,plain,(
    ! [X17] :
      ( ( l1_lattices(X17)
        | ~ l3_lattices(X17) )
      & ( l2_lattices(X17)
        | ~ l3_lattices(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_lattices(esk5_0,esk6_0,esk7_0)
    | k2_lattices(esk5_0,esk6_0,esk7_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( r1_lattices(esk5_0,X1,esk7_0)
    | k1_lattices(esk5_0,X1,esk7_0) != esk7_0
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_10])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v9_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | k2_lattices(X12,X13,k1_lattices(X12,X13,X14)) = X13
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk3_1(X12),u1_struct_0(X12))
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk4_1(X12),u1_struct_0(X12))
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( k2_lattices(X12,esk3_1(X12),k1_lattices(X12,esk3_1(X12),esk4_1(X12))) != esk3_1(X12)
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( k2_lattices(esk5_0,esk6_0,esk7_0) = esk6_0
    | k1_lattices(esk5_0,esk6_0,esk7_0) = esk7_0
    | ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_20,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( k2_lattices(esk5_0,esk6_0,esk7_0) != esk6_0
    | k1_lattices(esk5_0,esk6_0,esk7_0) != esk7_0
    | ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_14])])).

cnf(c_0_23,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k1_lattices(esk5_0,esk6_0,esk7_0) = esk7_0
    | k2_lattices(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( v9_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_26,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v8_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | k1_lattices(X7,k2_lattices(X7,X8,X9),X9) = X9
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( m1_subset_1(esk1_1(X7),u1_struct_0(X7))
        | v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( m1_subset_1(esk2_1(X7),u1_struct_0(X7))
        | v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( k1_lattices(X7,k2_lattices(X7,esk1_1(X7),esk2_1(X7)),esk2_1(X7)) != esk2_1(X7)
        | v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_27,negated_conjecture,
    ( k2_lattices(esk5_0,esk6_0,esk7_0) != esk6_0
    | k1_lattices(esk5_0,esk6_0,esk7_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21])])).

cnf(c_0_28,negated_conjecture,
    ( k2_lattices(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_21]),c_0_9]),c_0_14])]),c_0_10])).

cnf(c_0_29,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v8_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( k1_lattices(esk5_0,esk6_0,esk7_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_30]),c_0_21]),c_0_9]),c_0_14])]),c_0_10]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t21_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.19/0.37  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.19/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.37  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 0.19/0.37  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.19/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2))))), inference(assume_negation,[status(cth)],[t21_lattices])).
% 0.19/0.37  fof(c_0_6, plain, ![X4, X5, X6]:((~r1_lattices(X4,X5,X6)|k1_lattices(X4,X5,X6)=X6|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|(v2_struct_0(X4)|~l2_lattices(X4)))&(k1_lattices(X4,X5,X6)!=X6|r1_lattices(X4,X5,X6)|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|(v2_struct_0(X4)|~l2_lattices(X4)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.19/0.37  fof(c_0_7, negated_conjecture, ((((~v2_struct_0(esk5_0)&v8_lattices(esk5_0))&v9_lattices(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&((~r1_lattices(esk5_0,esk6_0,esk7_0)|k2_lattices(esk5_0,esk6_0,esk7_0)!=esk6_0)&(r1_lattices(esk5_0,esk6_0,esk7_0)|k2_lattices(esk5_0,esk6_0,esk7_0)=esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.19/0.37  cnf(c_0_8, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_10, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_11, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (k1_lattices(esk5_0,X1,esk7_0)=esk7_0|~r1_lattices(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])).
% 0.19/0.37  cnf(c_0_13, negated_conjecture, (r1_lattices(esk5_0,esk6_0,esk7_0)|k2_lattices(esk5_0,esk6_0,esk7_0)=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_15, plain, ![X17]:((l1_lattices(X17)|~l3_lattices(X17))&(l2_lattices(X17)|~l3_lattices(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (~r1_lattices(esk5_0,esk6_0,esk7_0)|k2_lattices(esk5_0,esk6_0,esk7_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (r1_lattices(esk5_0,X1,esk7_0)|k1_lattices(esk5_0,X1,esk7_0)!=esk7_0|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_9]), c_0_10])).
% 0.19/0.37  fof(c_0_18, plain, ![X12, X13, X14]:((~v9_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|k2_lattices(X12,X13,k1_lattices(X12,X13,X14))=X13))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk3_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk4_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&(k2_lattices(X12,esk3_1(X12),k1_lattices(X12,esk3_1(X12),esk4_1(X12)))!=esk3_1(X12)|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (k2_lattices(esk5_0,esk6_0,esk7_0)=esk6_0|k1_lattices(esk5_0,esk6_0,esk7_0)=esk7_0|~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.19/0.37  cnf(c_0_20, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (k2_lattices(esk5_0,esk6_0,esk7_0)!=esk6_0|k1_lattices(esk5_0,esk6_0,esk7_0)!=esk7_0|~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_14])])).
% 0.19/0.37  cnf(c_0_23, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k1_lattices(esk5_0,esk6_0,esk7_0)=esk7_0|k2_lattices(esk5_0,esk6_0,esk7_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (v9_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_26, plain, ![X7, X8, X9]:((~v8_lattices(X7)|(~m1_subset_1(X8,u1_struct_0(X7))|(~m1_subset_1(X9,u1_struct_0(X7))|k1_lattices(X7,k2_lattices(X7,X8,X9),X9)=X9))|(v2_struct_0(X7)|~l3_lattices(X7)))&((m1_subset_1(esk1_1(X7),u1_struct_0(X7))|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))&((m1_subset_1(esk2_1(X7),u1_struct_0(X7))|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))&(k1_lattices(X7,k2_lattices(X7,esk1_1(X7),esk2_1(X7)),esk2_1(X7))!=esk2_1(X7)|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k2_lattices(esk5_0,esk6_0,esk7_0)!=esk6_0|k1_lattices(esk5_0,esk6_0,esk7_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k2_lattices(esk5_0,esk6_0,esk7_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_21]), c_0_9]), c_0_14])]), c_0_10])).
% 0.19/0.37  cnf(c_0_29, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (v8_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (k1_lattices(esk5_0,esk6_0,esk7_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28])])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_30]), c_0_21]), c_0_9]), c_0_14])]), c_0_10]), c_0_31]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 33
% 0.19/0.37  # Proof object clause steps            : 22
% 0.19/0.37  # Proof object formula steps           : 11
% 0.19/0.37  # Proof object conjectures             : 20
% 0.19/0.37  # Proof object clause conjectures      : 17
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 5
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 25
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 5
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 20
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 20
% 0.19/0.37  # Processed clauses                    : 34
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 1
% 0.19/0.37  # ...remaining for further processing  : 32
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 2
% 0.19/0.37  # Backward-rewritten                   : 4
% 0.19/0.37  # Generated clauses                    : 25
% 0.19/0.37  # ...of the previous two non-trivial   : 19
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 25
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
% 0.19/0.37  #    Positive orientable unit clauses  : 6
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 17
% 0.19/0.37  # Current number of unprocessed clauses: 4
% 0.19/0.37  # ...number of literals in the above   : 9
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 6
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 79
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 31
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2109
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.033 s
% 0.19/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
