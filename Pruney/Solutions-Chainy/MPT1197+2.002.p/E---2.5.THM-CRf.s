%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:22 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 104 expanded)
%              Number of clauses        :   22 (  34 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  173 ( 566 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

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

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

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

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v6_lattices(X1)
          & v8_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r1_lattices(X1,k4_lattices(X1,X2,X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_lattices])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v6_lattices(esk3_0)
    & v8_lattices(esk3_0)
    & l3_lattices(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ~ r1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ r1_lattices(X7,X8,X9)
        | k1_lattices(X7,X8,X9) = X9
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ l2_lattices(X7) )
      & ( k1_lattices(X7,X8,X9) != X9
        | r1_lattices(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ l2_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

fof(c_0_10,plain,(
    ! [X19,X20,X21] :
      ( v2_struct_0(X19)
      | ~ v6_lattices(X19)
      | ~ l1_lattices(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | k4_lattices(X19,X20,X21) = k2_lattices(X19,X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_11,plain,(
    ! [X4,X5,X6] :
      ( v2_struct_0(X4)
      | ~ v6_lattices(X4)
      | ~ l1_lattices(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | k4_lattices(X4,X5,X6) = k4_lattices(X4,X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( k1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk4_0) != esk4_0
    | ~ l2_lattices(esk3_0)
    | ~ m1_subset_1(k4_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,plain,
    ( k4_lattices(X1,X2,X3) = k2_lattices(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v6_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_22,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v8_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | k1_lattices(X10,k2_lattices(X10,X11,X12),X12) = X12
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk1_1(X10),u1_struct_0(X10))
        | v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( m1_subset_1(esk2_1(X10),u1_struct_0(X10))
        | v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) )
      & ( k1_lattices(X10,k2_lattices(X10,esk1_1(X10),esk2_1(X10)),esk2_1(X10)) != esk2_1(X10)
        | v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v6_lattices(X15)
      | ~ l1_lattices(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | ~ m1_subset_1(X17,u1_struct_0(X15))
      | m1_subset_1(k4_lattices(X15,X16,X17),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_24,negated_conjecture,
    ( k1_lattices(esk3_0,k2_lattices(esk3_0,esk5_0,esk4_0),esk4_0) != esk4_0
    | ~ l2_lattices(esk3_0)
    | ~ m1_subset_1(k2_lattices(esk3_0,esk5_0,esk4_0),u1_struct_0(esk3_0))
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_14]),c_0_20]),c_0_21])]),c_0_15])).

cnf(c_0_25,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v8_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( ~ l2_lattices(esk3_0)
    | ~ m1_subset_1(k2_lattices(esk3_0,esk5_0,esk4_0),u1_struct_0(esk3_0))
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_14]),c_0_20])]),c_0_15])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_lattices(X1)
    | ~ v6_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_16])).

fof(c_0_31,plain,(
    ! [X18] :
      ( ( l1_lattices(X18)
        | ~ l3_lattices(X18) )
      & ( l2_lattices(X18)
        | ~ l3_lattices(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_32,negated_conjecture,
    ( ~ l2_lattices(esk3_0)
    | ~ l1_lattices(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_14]),c_0_20]),c_0_21])]),c_0_15])).

cnf(c_0_33,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( ~ l1_lattices(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27])])).

cnf(c_0_35,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:36:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t23_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,k4_lattices(X1,X2,X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 0.12/0.37  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 0.12/0.37  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.12/0.37  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 0.12/0.37  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 0.12/0.37  fof(dt_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_lattices)).
% 0.12/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.12/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r1_lattices(X1,k4_lattices(X1,X2,X3),X2))))), inference(assume_negation,[status(cth)],[t23_lattices])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ((((~v2_struct_0(esk3_0)&v6_lattices(esk3_0))&v8_lattices(esk3_0))&l3_lattices(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&~r1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X7, X8, X9]:((~r1_lattices(X7,X8,X9)|k1_lattices(X7,X8,X9)=X9|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~l2_lattices(X7)))&(k1_lattices(X7,X8,X9)!=X9|r1_lattices(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~l2_lattices(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.12/0.37  fof(c_0_10, plain, ![X19, X20, X21]:(v2_struct_0(X19)|~v6_lattices(X19)|~l1_lattices(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|k4_lattices(X19,X20,X21)=k2_lattices(X19,X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X4, X5, X6]:(v2_struct_0(X4)|~v6_lattices(X4)|~l1_lattices(X4)|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X4))|k4_lattices(X4,X5,X6)=k4_lattices(X4,X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (~r1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_13, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_16, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_17, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (k1_lattices(esk3_0,k4_lattices(esk3_0,esk4_0,esk5_0),esk4_0)!=esk4_0|~l2_lattices(esk3_0)|~m1_subset_1(k4_lattices(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])]), c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (k4_lattices(X1,X2,X3)=k2_lattices(X1,X3,X2)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_lattices(X1)|~v6_lattices(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v6_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_22, plain, ![X10, X11, X12]:((~v8_lattices(X10)|(~m1_subset_1(X11,u1_struct_0(X10))|(~m1_subset_1(X12,u1_struct_0(X10))|k1_lattices(X10,k2_lattices(X10,X11,X12),X12)=X12))|(v2_struct_0(X10)|~l3_lattices(X10)))&((m1_subset_1(esk1_1(X10),u1_struct_0(X10))|v8_lattices(X10)|(v2_struct_0(X10)|~l3_lattices(X10)))&((m1_subset_1(esk2_1(X10),u1_struct_0(X10))|v8_lattices(X10)|(v2_struct_0(X10)|~l3_lattices(X10)))&(k1_lattices(X10,k2_lattices(X10,esk1_1(X10),esk2_1(X10)),esk2_1(X10))!=esk2_1(X10)|v8_lattices(X10)|(v2_struct_0(X10)|~l3_lattices(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.12/0.37  fof(c_0_23, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v6_lattices(X15)|~l1_lattices(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))|m1_subset_1(k4_lattices(X15,X16,X17),u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (k1_lattices(esk3_0,k2_lattices(esk3_0,esk5_0,esk4_0),esk4_0)!=esk4_0|~l2_lattices(esk3_0)|~m1_subset_1(k2_lattices(esk3_0,esk5_0,esk4_0),u1_struct_0(esk3_0))|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_14]), c_0_20]), c_0_21])]), c_0_15])).
% 0.12/0.37  cnf(c_0_25, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (v8_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (l3_lattices(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_28, plain, (v2_struct_0(X1)|m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (~l2_lattices(esk3_0)|~m1_subset_1(k2_lattices(esk3_0,esk5_0,esk4_0),u1_struct_0(esk3_0))|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_14]), c_0_20])]), c_0_15])).
% 0.12/0.37  cnf(c_0_30, plain, (m1_subset_1(k2_lattices(X1,X2,X3),u1_struct_0(X1))|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_lattices(X1)|~v6_lattices(X1)), inference(spm,[status(thm)],[c_0_28, c_0_16])).
% 0.12/0.37  fof(c_0_31, plain, ![X18]:((l1_lattices(X18)|~l3_lattices(X18))&(l2_lattices(X18)|~l3_lattices(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (~l2_lattices(esk3_0)|~l1_lattices(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_14]), c_0_20]), c_0_21])]), c_0_15])).
% 0.12/0.37  cnf(c_0_33, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (~l1_lattices(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27])])).
% 0.12/0.37  cnf(c_0_35, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_27])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 37
% 0.12/0.37  # Proof object clause steps            : 22
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 16
% 0.12/0.37  # Proof object clause conjectures      : 13
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 23
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 18
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 18
% 0.12/0.37  # Processed clauses                    : 52
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 6
% 0.12/0.37  # ...remaining for further processing  : 46
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 3
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 22
% 0.12/0.37  # ...of the previous two non-trivial   : 19
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 22
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 25
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 17
% 0.12/0.37  # Current number of unprocessed clauses: 3
% 0.12/0.37  # ...number of literals in the above   : 18
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 21
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 143
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 45
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 9
% 0.12/0.37  # Unit Clause-clause subsumption calls : 3
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 0
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2424
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.028 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
