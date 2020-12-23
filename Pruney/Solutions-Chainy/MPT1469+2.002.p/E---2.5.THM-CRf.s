%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 134 expanded)
%              Number of clauses        :   23 (  53 expanded)
%              Number of leaves         :    8 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 442 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_lattice3,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
         => ( r1_lattices(k1_lattice3(X1),X2,X3)
          <=> r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_lattice3)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(dt_k1_lattice3,axiom,(
    ! [X1] :
      ( v3_lattices(k1_lattice3(X1))
      & l3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

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

fof(fc1_lattice3,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k1_lattice3(X1))
      & v3_lattices(k1_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(t1_lattice3,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
         => ( k1_lattices(k1_lattice3(X1),X2,X3) = k2_xboole_0(X2,X3)
            & k2_lattices(k1_lattice3(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_lattice3)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
           => ( r1_lattices(k1_lattice3(X1),X2,X3)
            <=> r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t2_lattice3])).

fof(c_0_9,plain,(
    ! [X11] :
      ( ( l1_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( l2_lattices(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_10,plain,(
    ! [X12] :
      ( v3_lattices(k1_lattice3(X12))
      & l3_lattices(k1_lattice3(X12)) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_lattice3])).

fof(c_0_11,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r1_lattices(X8,X9,X10)
        | k1_lattices(X8,X9,X10) = X10
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) )
      & ( k1_lattices(X8,X9,X10) != X10
        | r1_lattices(X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X8))
        | ~ m1_subset_1(X9,u1_struct_0(X8))
        | v2_struct_0(X8)
        | ~ l2_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).

fof(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0)))
    & ( ~ r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)
      | ~ r1_tarski(esk2_0,esk3_0) )
    & ( r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)
      | r1_tarski(esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( l3_lattices(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X13] :
      ( ~ v2_struct_0(k1_lattice3(X13))
      & v3_lattices(k1_lattice3(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).

fof(c_0_16,plain,(
    ! [X14,X15,X16] :
      ( ( k1_lattices(k1_lattice3(X14),X15,X16) = k2_xboole_0(X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(k1_lattice3(X14)))
        | ~ m1_subset_1(X15,u1_struct_0(k1_lattice3(X14))) )
      & ( k2_lattices(k1_lattice3(X14),X15,X16) = k3_xboole_0(X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(k1_lattice3(X14)))
        | ~ m1_subset_1(X15,u1_struct_0(k1_lattice3(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_lattice3])])])])).

cnf(c_0_17,plain,
    ( k1_lattices(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( l2_lattices(k1_lattice3(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( ~ v2_struct_0(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k1_lattices(k1_lattice3(X1),X2,X3) = k2_xboole_0(X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( k1_lattices(k1_lattice3(esk1_0),X1,esk3_0) = esk3_0
    | ~ r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)
    | r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( k1_lattices(k1_lattice3(esk1_0),X1,esk3_0) = k2_xboole_0(X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

fof(c_0_26,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k2_xboole_0(X4,X5) = X5 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_27,negated_conjecture,
    ( k1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) = esk3_0
    | r1_tarski(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_28,negated_conjecture,
    ( k1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) = k2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,plain,(
    ! [X6,X7] : r1_tarski(X6,k2_xboole_0(X6,X7)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_31,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k1_lattices(X1,X2,X3) != X3
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)
    | k1_lattices(k1_lattice3(esk1_0),X1,esk3_0) != esk3_0
    | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( k1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_28,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)
    | ~ r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_24])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:55:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.19/0.37  # and selection function SelectLComplex.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t2_lattice3, conjecture, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))=>(r1_lattices(k1_lattice3(X1),X2,X3)<=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_lattice3)).
% 0.19/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.19/0.37  fof(dt_k1_lattice3, axiom, ![X1]:(v3_lattices(k1_lattice3(X1))&l3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_lattice3)).
% 0.19/0.37  fof(d3_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l2_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k1_lattices(X1,X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 0.19/0.37  fof(fc1_lattice3, axiom, ![X1]:(~(v2_struct_0(k1_lattice3(X1)))&v3_lattices(k1_lattice3(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_lattice3)).
% 0.19/0.37  fof(t1_lattice3, axiom, ![X1, X2]:(m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))=>(k1_lattices(k1_lattice3(X1),X2,X3)=k2_xboole_0(X2,X3)&k2_lattices(k1_lattice3(X1),X2,X3)=k3_xboole_0(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_lattice3)).
% 0.19/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.37  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.37  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))=>(r1_lattices(k1_lattice3(X1),X2,X3)<=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t2_lattice3])).
% 0.19/0.37  fof(c_0_9, plain, ![X11]:((l1_lattices(X11)|~l3_lattices(X11))&(l2_lattices(X11)|~l3_lattices(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.19/0.37  fof(c_0_10, plain, ![X12]:(v3_lattices(k1_lattice3(X12))&l3_lattices(k1_lattice3(X12))), inference(variable_rename,[status(thm)],[dt_k1_lattice3])).
% 0.19/0.37  fof(c_0_11, plain, ![X8, X9, X10]:((~r1_lattices(X8,X9,X10)|k1_lattices(X8,X9,X10)=X10|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~l2_lattices(X8)))&(k1_lattices(X8,X9,X10)!=X10|r1_lattices(X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X8))|~m1_subset_1(X9,u1_struct_0(X8))|(v2_struct_0(X8)|~l2_lattices(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattices])])])])])).
% 0.19/0.37  fof(c_0_12, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0)))&((~r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)|~r1_tarski(esk2_0,esk3_0))&(r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)|r1_tarski(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.37  cnf(c_0_13, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, plain, (l3_lattices(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_15, plain, ![X13]:(~v2_struct_0(k1_lattice3(X13))&v3_lattices(k1_lattice3(X13))), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_lattice3])])).
% 0.19/0.37  fof(c_0_16, plain, ![X14, X15, X16]:((k1_lattices(k1_lattice3(X14),X15,X16)=k2_xboole_0(X15,X16)|~m1_subset_1(X16,u1_struct_0(k1_lattice3(X14)))|~m1_subset_1(X15,u1_struct_0(k1_lattice3(X14))))&(k2_lattices(k1_lattice3(X14),X15,X16)=k3_xboole_0(X15,X16)|~m1_subset_1(X16,u1_struct_0(k1_lattice3(X14)))|~m1_subset_1(X15,u1_struct_0(k1_lattice3(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_lattice3])])])])).
% 0.19/0.37  cnf(c_0_17, plain, (k1_lattices(X1,X2,X3)=X3|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k1_lattice3(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_19, plain, (l2_lattices(k1_lattice3(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.37  cnf(c_0_20, plain, (~v2_struct_0(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_21, plain, (k1_lattices(k1_lattice3(X1),X2,X3)=k2_xboole_0(X2,X3)|~m1_subset_1(X3,u1_struct_0(k1_lattice3(X1)))|~m1_subset_1(X2,u1_struct_0(k1_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (k1_lattices(k1_lattice3(esk1_0),X1,esk3_0)=esk3_0|~r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)|r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k1_lattice3(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (k1_lattices(k1_lattice3(esk1_0),X1,esk3_0)=k2_xboole_0(X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 0.19/0.37  fof(c_0_26, plain, ![X4, X5]:(~r1_tarski(X4,X5)|k2_xboole_0(X4,X5)=X5), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)=esk3_0|r1_tarski(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)=k2_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.19/0.37  cnf(c_0_29, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  fof(c_0_30, plain, ![X6, X7]:r1_tarski(X6,k2_xboole_0(X6,X7)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.37  cnf(c_0_31, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k1_lattices(X1,X2,X3)!=X3|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l2_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (k2_xboole_0(esk2_0,esk3_0)=esk3_0), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.37  cnf(c_0_33, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),X1,esk3_0)|k1_lattices(k1_lattice3(esk1_0),X1,esk3_0)!=esk3_0|~m1_subset_1(X1,u1_struct_0(k1_lattice3(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (k1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[c_0_28, c_0_32])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (~r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)|~r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_32])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (r1_lattices(k1_lattice3(esk1_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_24])])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])]), c_0_38])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 40
% 0.19/0.37  # Proof object clause steps            : 23
% 0.19/0.37  # Proof object formula steps           : 17
% 0.19/0.37  # Proof object conjectures             : 17
% 0.19/0.37  # Proof object clause conjectures      : 14
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 12
% 0.19/0.37  # Proof object initial formulas used   : 8
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 17
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 8
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 16
% 0.19/0.37  # Processed clauses                    : 52
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 2
% 0.19/0.37  # ...remaining for further processing  : 48
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 6
% 0.19/0.37  # Generated clauses                    : 29
% 0.19/0.37  # ...of the previous two non-trivial   : 26
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 29
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
% 0.19/0.37  # Current number of processed clauses  : 27
% 0.19/0.37  #    Positive orientable unit clauses  : 13
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 13
% 0.19/0.37  # Current number of unprocessed clauses: 4
% 0.19/0.37  # ...number of literals in the above   : 8
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 21
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 169
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 87
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.37  # Unit Clause-clause subsumption calls : 11
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1603
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.032 s
% 0.19/0.37  # System time              : 0.002 s
% 0.19/0.37  # Total time               : 0.034 s
% 0.19/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
