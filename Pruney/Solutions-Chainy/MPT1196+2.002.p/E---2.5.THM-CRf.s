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
% DateTime   : Thu Dec  3 11:10:22 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   33 (  91 expanded)
%              Number of clauses        :   20 (  31 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  163 ( 595 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_lattices(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,X2,k1_lattices(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_lattices)).

fof(dt_k1_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r1_lattices(X1,X2,k1_lattices(X1,X2,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_lattices])).

fof(c_0_7,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ l2_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | m1_subset_1(k1_lattices(X17,X18,X19),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v5_lattices(esk5_0)
    & v6_lattices(esk5_0)
    & v8_lattices(esk5_0)
    & v9_lattices(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & ~ r1_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,esk6_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
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

cnf(c_0_10,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
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

fof(c_0_14,plain,(
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

cnf(c_0_15,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(k1_lattices(esk5_0,X1,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_17,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v8_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v9_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( r1_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk7_0))
    | k1_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk7_0)) != k1_lattices(esk5_0,X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( k1_lattices(esk5_0,k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk7_0)),k1_lattices(esk5_0,X2,esk7_0)) = k1_lattices(esk5_0,X2,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_16]),c_0_18]),c_0_19])]),c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X1,esk7_0)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_11]),c_0_21]),c_0_19])]),c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k1_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,esk6_0,esk7_0)) != k1_lattices(esk5_0,esk6_0,esk7_0)
    | ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( k1_lattices(esk5_0,X1,k1_lattices(esk5_0,X1,esk7_0)) = k1_lattices(esk5_0,X1,esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_29,plain,(
    ! [X20] :
      ( ( l1_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( l2_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_30,negated_conjecture,
    ( ~ l2_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])])).

cnf(c_0_31,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:44:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.027 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t22_lattices, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v5_lattices(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,X2,k1_lattices(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_lattices)).
% 0.12/0.38  fof(dt_k1_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_lattices)).
% 0.12/0.38  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.12/0.38  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 0.12/0.38  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 0.12/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.12/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v5_lattices(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,X2,k1_lattices(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t22_lattices])).
% 0.12/0.38  fof(c_0_7, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~l2_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|m1_subset_1(k1_lattices(X17,X18,X19),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).
% 0.12/0.38  fof(c_0_8, negated_conjecture, ((((((~v2_struct_0(esk5_0)&v5_lattices(esk5_0))&v6_lattices(esk5_0))&v8_lattices(esk5_0))&v9_lattices(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&~r1_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,esk6_0,esk7_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.12/0.38  fof(c_0_9, plain, ![X4, X5, X6]:((~r1_lattices(X4,X5,X6)|k1_lattices(X4,X5,X6)=X6|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|(v2_struct_0(X4)|~l2_lattices(X4)))&(k1_lattices(X4,X5,X6)!=X6|r1_lattices(X4,X5,X6)|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|(v2_struct_0(X4)|~l2_lattices(X4)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.12/0.38  cnf(c_0_10, plain, (v2_struct_0(X1)|m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_12, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  fof(c_0_13, plain, ![X7, X8, X9]:((~v8_lattices(X7)|(~m1_subset_1(X8,u1_struct_0(X7))|(~m1_subset_1(X9,u1_struct_0(X7))|k1_lattices(X7,k2_lattices(X7,X8,X9),X9)=X9))|(v2_struct_0(X7)|~l3_lattices(X7)))&((m1_subset_1(esk1_1(X7),u1_struct_0(X7))|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))&((m1_subset_1(esk2_1(X7),u1_struct_0(X7))|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))&(k1_lattices(X7,k2_lattices(X7,esk1_1(X7),esk2_1(X7)),esk2_1(X7))!=esk2_1(X7)|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.12/0.38  fof(c_0_14, plain, ![X12, X13, X14]:((~v9_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|k2_lattices(X12,X13,k1_lattices(X12,X13,X14))=X13))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk3_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk4_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&(k2_lattices(X12,esk3_1(X12),k1_lattices(X12,esk3_1(X12),esk4_1(X12)))!=esk3_1(X12)|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.12/0.38  cnf(c_0_15, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(k1_lattices(esk5_0,X1,esk7_0),u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])).
% 0.12/0.38  cnf(c_0_17, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (v8_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_20, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (v9_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (~r1_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,esk6_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (r1_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk7_0))|k1_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk7_0))!=k1_lattices(esk5_0,X2,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_12])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (k1_lattices(esk5_0,k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk7_0)),k1_lattices(esk5_0,X2,esk7_0))=k1_lattices(esk5_0,X2,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_16]), c_0_18]), c_0_19])]), c_0_12])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X1,esk7_0))=X1|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_11]), c_0_21]), c_0_19])]), c_0_12])).
% 0.12/0.38  cnf(c_0_27, negated_conjecture, (k1_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,esk6_0,esk7_0))!=k1_lattices(esk5_0,esk6_0,esk7_0)|~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (k1_lattices(esk5_0,X1,k1_lattices(esk5_0,X1,esk7_0))=k1_lattices(esk5_0,X1,esk7_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l2_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.38  fof(c_0_29, plain, ![X20]:((l1_lattices(X20)|~l3_lattices(X20))&(l2_lattices(X20)|~l3_lattices(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.12/0.38  cnf(c_0_30, negated_conjecture, (~l2_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24])])).
% 0.12/0.38  cnf(c_0_31, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_19])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 33
% 0.12/0.38  # Proof object clause steps            : 20
% 0.12/0.38  # Proof object formula steps           : 13
% 0.12/0.38  # Proof object conjectures             : 18
% 0.12/0.38  # Proof object clause conjectures      : 15
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 12
% 0.12/0.38  # Proof object initial formulas used   : 6
% 0.12/0.38  # Proof object generating inferences   : 8
% 0.12/0.38  # Proof object simplifying inferences  : 16
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 6
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 22
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 22
% 0.12/0.38  # Processed clauses                    : 102
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 27
% 0.12/0.38  # ...remaining for further processing  : 75
% 0.12/0.38  # Other redundant clauses eliminated   : 0
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 0
% 0.12/0.38  # Generated clauses                    : 99
% 0.12/0.38  # ...of the previous two non-trivial   : 87
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 99
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 0
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 53
% 0.12/0.38  #    Positive orientable unit clauses  : 7
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 43
% 0.12/0.38  # Current number of unprocessed clauses: 29
% 0.12/0.38  # ...number of literals in the above   : 161
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 22
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 623
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 145
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 27
% 0.12/0.38  # Unit Clause-clause subsumption calls : 27
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 0
% 0.12/0.38  # BW rewrite match successes           : 0
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 5248
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.032 s
% 0.12/0.38  # System time              : 0.005 s
% 0.12/0.38  # Total time               : 0.037 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
