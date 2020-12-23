%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:34 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   34 (  83 expanded)
%              Number of clauses        :   21 (  33 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 220 expanded)
%              Number of equality atoms :   34 (  75 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_waybel_9,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_9)).

fof(dt_k3_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v6_waybel_0(k3_waybel_9(X1),X1)
        & l1_waybel_0(k3_waybel_9(X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_9)).

fof(d6_waybel_9,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( v6_waybel_0(X2,X1)
            & l1_waybel_0(X2,X1) )
         => ( X2 = k3_waybel_9(X1)
          <=> ( u1_struct_0(X2) = u1_struct_0(X1)
              & u1_orders_2(X2) = k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))
              & u1_waybel_0(X1,X2) = k3_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_waybel_9)).

fof(dt_k7_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(k7_lattice3(X1))
        & l1_orders_2(k7_lattice3(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_lattice3)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1))) = g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1))) ) ),
    inference(assume_negation,[status(cth)],[t11_waybel_9])).

fof(c_0_7,plain,(
    ! [X8] :
      ( ( v6_waybel_0(k3_waybel_9(X8),X8)
        | ~ l1_orders_2(X8) )
      & ( l1_waybel_0(k3_waybel_9(X8),X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_waybel_9])])])).

fof(c_0_8,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X6,X7] :
      ( ( u1_struct_0(X7) = u1_struct_0(X6)
        | X7 != k3_waybel_9(X6)
        | ~ v6_waybel_0(X7,X6)
        | ~ l1_waybel_0(X7,X6)
        | ~ l1_orders_2(X6) )
      & ( u1_orders_2(X7) = k3_relset_1(u1_struct_0(X6),u1_struct_0(X6),u1_orders_2(X6))
        | X7 != k3_waybel_9(X6)
        | ~ v6_waybel_0(X7,X6)
        | ~ l1_waybel_0(X7,X6)
        | ~ l1_orders_2(X6) )
      & ( u1_waybel_0(X6,X7) = k3_struct_0(X6)
        | X7 != k3_waybel_9(X6)
        | ~ v6_waybel_0(X7,X6)
        | ~ l1_waybel_0(X7,X6)
        | ~ l1_orders_2(X6) )
      & ( u1_struct_0(X7) != u1_struct_0(X6)
        | u1_orders_2(X7) != k3_relset_1(u1_struct_0(X6),u1_struct_0(X6),u1_orders_2(X6))
        | u1_waybel_0(X6,X7) != k3_struct_0(X6)
        | X7 = k3_waybel_9(X6)
        | ~ v6_waybel_0(X7,X6)
        | ~ l1_waybel_0(X7,X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_waybel_9])])])])).

cnf(c_0_10,plain,
    ( l1_waybel_0(k3_waybel_9(X1),X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v6_waybel_0(k3_waybel_9(X1),X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X5] :
      ( ( v1_orders_2(k7_lattice3(X5))
        | ~ l1_orders_2(X5) )
      & ( l1_orders_2(k7_lattice3(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).

cnf(c_0_14,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | X1 != k3_waybel_9(X2)
    | ~ v6_waybel_0(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( l1_waybel_0(k3_waybel_9(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v6_waybel_0(k3_waybel_9(esk1_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

fof(c_0_17,plain,(
    ! [X3] :
      ( ~ l1_orders_2(X3)
      | ~ v1_orders_2(X3)
      | X3 = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_18,plain,
    ( v1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( l1_orders_2(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X4] :
      ( ~ l1_orders_2(X4)
      | k7_lattice3(X4) = g1_orders_2(u1_struct_0(X4),k3_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(k3_waybel_9(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_23,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_26,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( u1_orders_2(X1) = k3_relset_1(u1_struct_0(X2),u1_struct_0(X2),u1_orders_2(X2))
    | X1 != k3_waybel_9(X2)
    | ~ v6_waybel_0(X1,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k3_waybel_9(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_30,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = u1_orders_2(k3_waybel_9(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_32,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k3_waybel_9(esk1_0))) != k7_lattice3(esk1_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:20:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.15/0.38  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.15/0.38  # and selection function SelectComplexG.
% 0.15/0.38  #
% 0.15/0.38  # Preprocessing time       : 0.027 s
% 0.15/0.38  
% 0.15/0.38  # Proof found!
% 0.15/0.38  # SZS status Theorem
% 0.15/0.38  # SZS output start CNFRefutation
% 0.15/0.38  fof(t11_waybel_9, conjecture, ![X1]:(l1_orders_2(X1)=>g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1)))=g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_9)).
% 0.15/0.38  fof(dt_k3_waybel_9, axiom, ![X1]:(l1_orders_2(X1)=>(v6_waybel_0(k3_waybel_9(X1),X1)&l1_waybel_0(k3_waybel_9(X1),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_waybel_9)).
% 0.15/0.38  fof(d6_waybel_9, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:((v6_waybel_0(X2,X1)&l1_waybel_0(X2,X1))=>(X2=k3_waybel_9(X1)<=>((u1_struct_0(X2)=u1_struct_0(X1)&u1_orders_2(X2)=k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))&u1_waybel_0(X1,X2)=k3_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_waybel_9)).
% 0.15/0.38  fof(dt_k7_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(k7_lattice3(X1))&l1_orders_2(k7_lattice3(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattice3)).
% 0.15/0.38  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.15/0.38  fof(d5_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>k7_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_lattice3)).
% 0.15/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>g1_orders_2(u1_struct_0(k7_lattice3(X1)),u1_orders_2(k7_lattice3(X1)))=g1_orders_2(u1_struct_0(k3_waybel_9(X1)),u1_orders_2(k3_waybel_9(X1))))), inference(assume_negation,[status(cth)],[t11_waybel_9])).
% 0.15/0.38  fof(c_0_7, plain, ![X8]:((v6_waybel_0(k3_waybel_9(X8),X8)|~l1_orders_2(X8))&(l1_waybel_0(k3_waybel_9(X8),X8)|~l1_orders_2(X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_waybel_9])])])).
% 0.15/0.38  fof(c_0_8, negated_conjecture, (l1_orders_2(esk1_0)&g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0)))!=g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.15/0.38  fof(c_0_9, plain, ![X6, X7]:((((u1_struct_0(X7)=u1_struct_0(X6)|X7!=k3_waybel_9(X6)|(~v6_waybel_0(X7,X6)|~l1_waybel_0(X7,X6))|~l1_orders_2(X6))&(u1_orders_2(X7)=k3_relset_1(u1_struct_0(X6),u1_struct_0(X6),u1_orders_2(X6))|X7!=k3_waybel_9(X6)|(~v6_waybel_0(X7,X6)|~l1_waybel_0(X7,X6))|~l1_orders_2(X6)))&(u1_waybel_0(X6,X7)=k3_struct_0(X6)|X7!=k3_waybel_9(X6)|(~v6_waybel_0(X7,X6)|~l1_waybel_0(X7,X6))|~l1_orders_2(X6)))&(u1_struct_0(X7)!=u1_struct_0(X6)|u1_orders_2(X7)!=k3_relset_1(u1_struct_0(X6),u1_struct_0(X6),u1_orders_2(X6))|u1_waybel_0(X6,X7)!=k3_struct_0(X6)|X7=k3_waybel_9(X6)|(~v6_waybel_0(X7,X6)|~l1_waybel_0(X7,X6))|~l1_orders_2(X6))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_waybel_9])])])])).
% 0.15/0.38  cnf(c_0_10, plain, (l1_waybel_0(k3_waybel_9(X1),X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.38  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.38  cnf(c_0_12, plain, (v6_waybel_0(k3_waybel_9(X1),X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.15/0.38  fof(c_0_13, plain, ![X5]:((v1_orders_2(k7_lattice3(X5))|~l1_orders_2(X5))&(l1_orders_2(k7_lattice3(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_lattice3])])])).
% 0.15/0.38  cnf(c_0_14, plain, (u1_struct_0(X1)=u1_struct_0(X2)|X1!=k3_waybel_9(X2)|~v6_waybel_0(X1,X2)|~l1_waybel_0(X1,X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  cnf(c_0_15, negated_conjecture, (l1_waybel_0(k3_waybel_9(esk1_0),esk1_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.15/0.38  cnf(c_0_16, negated_conjecture, (v6_waybel_0(k3_waybel_9(esk1_0),esk1_0)), inference(spm,[status(thm)],[c_0_12, c_0_11])).
% 0.15/0.38  fof(c_0_17, plain, ![X3]:(~l1_orders_2(X3)|(~v1_orders_2(X3)|X3=g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.15/0.38  cnf(c_0_18, plain, (v1_orders_2(k7_lattice3(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.38  cnf(c_0_19, plain, (l1_orders_2(k7_lattice3(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.38  fof(c_0_20, plain, ![X4]:(~l1_orders_2(X4)|k7_lattice3(X4)=g1_orders_2(u1_struct_0(X4),k3_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).
% 0.15/0.38  cnf(c_0_21, negated_conjecture, (g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0)))!=g1_orders_2(u1_struct_0(k3_waybel_9(esk1_0)),u1_orders_2(k3_waybel_9(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.15/0.38  cnf(c_0_22, negated_conjecture, (u1_struct_0(k3_waybel_9(esk1_0))=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_11])])).
% 0.15/0.38  cnf(c_0_23, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.15/0.38  cnf(c_0_24, negated_conjecture, (v1_orders_2(k7_lattice3(esk1_0))), inference(spm,[status(thm)],[c_0_18, c_0_11])).
% 0.15/0.38  cnf(c_0_25, negated_conjecture, (l1_orders_2(k7_lattice3(esk1_0))), inference(spm,[status(thm)],[c_0_19, c_0_11])).
% 0.15/0.38  cnf(c_0_26, plain, (k7_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.15/0.38  cnf(c_0_27, plain, (u1_orders_2(X1)=k3_relset_1(u1_struct_0(X2),u1_struct_0(X2),u1_orders_2(X2))|X1!=k3_waybel_9(X2)|~v6_waybel_0(X1,X2)|~l1_waybel_0(X1,X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.15/0.38  cnf(c_0_28, negated_conjecture, (g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0)))!=g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k3_waybel_9(esk1_0)))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.15/0.38  cnf(c_0_29, negated_conjecture, (g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0)))=k7_lattice3(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.15/0.38  cnf(c_0_30, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)))=k7_lattice3(esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_11])).
% 0.15/0.38  cnf(c_0_31, negated_conjecture, (k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))=u1_orders_2(k3_waybel_9(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_15]), c_0_16]), c_0_11])])).
% 0.15/0.38  cnf(c_0_32, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k3_waybel_9(esk1_0)))!=k7_lattice3(esk1_0)), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.15/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), ['proof']).
% 0.15/0.38  # SZS output end CNFRefutation
% 0.15/0.38  # Proof object total steps             : 34
% 0.15/0.38  # Proof object clause steps            : 21
% 0.15/0.38  # Proof object formula steps           : 13
% 0.15/0.38  # Proof object conjectures             : 16
% 0.15/0.38  # Proof object clause conjectures      : 13
% 0.15/0.38  # Proof object formula conjectures     : 3
% 0.15/0.38  # Proof object initial clauses used    : 10
% 0.15/0.38  # Proof object initial formulas used   : 6
% 0.15/0.38  # Proof object generating inferences   : 8
% 0.15/0.38  # Proof object simplifying inferences  : 12
% 0.15/0.38  # Training examples: 0 positive, 0 negative
% 0.15/0.38  # Parsed axioms                        : 6
% 0.15/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.38  # Initial clauses                      : 12
% 0.15/0.38  # Removed in clause preprocessing      : 0
% 0.15/0.38  # Initial clauses in saturation        : 12
% 0.15/0.38  # Processed clauses                    : 45
% 0.15/0.38  # ...of these trivial                  : 0
% 0.15/0.38  # ...subsumed                          : 0
% 0.15/0.38  # ...remaining for further processing  : 45
% 0.15/0.38  # Other redundant clauses eliminated   : 0
% 0.15/0.38  # Clauses deleted for lack of memory   : 0
% 0.15/0.38  # Backward-subsumed                    : 0
% 0.15/0.38  # Backward-rewritten                   : 3
% 0.15/0.38  # Generated clauses                    : 73
% 0.15/0.38  # ...of the previous two non-trivial   : 74
% 0.15/0.38  # Contextual simplify-reflections      : 0
% 0.15/0.38  # Paramodulations                      : 73
% 0.15/0.38  # Factorizations                       : 0
% 0.15/0.38  # Equation resolutions                 : 0
% 0.15/0.38  # Propositional unsat checks           : 0
% 0.15/0.38  #    Propositional check models        : 0
% 0.15/0.38  #    Propositional check unsatisfiable : 0
% 0.15/0.38  #    Propositional clauses             : 0
% 0.15/0.38  #    Propositional clauses after purity: 0
% 0.15/0.38  #    Propositional unsat core size     : 0
% 0.15/0.38  #    Propositional preprocessing time  : 0.000
% 0.15/0.38  #    Propositional encoding time       : 0.000
% 0.15/0.38  #    Propositional solver time         : 0.000
% 0.15/0.38  #    Success case prop preproc time    : 0.000
% 0.15/0.38  #    Success case prop encoding time   : 0.000
% 0.15/0.38  #    Success case prop solver time     : 0.000
% 0.15/0.38  # Current number of processed clauses  : 42
% 0.15/0.38  #    Positive orientable unit clauses  : 31
% 0.15/0.38  #    Positive unorientable unit clauses: 0
% 0.15/0.38  #    Negative unit clauses             : 1
% 0.15/0.38  #    Non-unit-clauses                  : 10
% 0.15/0.38  # Current number of unprocessed clauses: 41
% 0.15/0.38  # ...number of literals in the above   : 59
% 0.15/0.38  # Current number of archived formulas  : 0
% 0.15/0.38  # Current number of archived clauses   : 3
% 0.15/0.38  # Clause-clause subsumption calls (NU) : 13
% 0.15/0.38  # Rec. Clause-clause subsumption calls : 3
% 0.15/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.15/0.38  # Unit Clause-clause subsumption calls : 11
% 0.15/0.38  # Rewrite failures with RHS unbound    : 0
% 0.15/0.38  # BW rewrite match attempts            : 49
% 0.15/0.38  # BW rewrite match successes           : 3
% 0.15/0.38  # Condensation attempts                : 0
% 0.15/0.38  # Condensation successes               : 0
% 0.15/0.38  # Termbank termtop insertions          : 2516
% 0.15/0.38  
% 0.15/0.38  # -------------------------------------------------
% 0.15/0.38  # User time                : 0.025 s
% 0.15/0.38  # System time              : 0.007 s
% 0.15/0.38  # Total time               : 0.032 s
% 0.15/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
