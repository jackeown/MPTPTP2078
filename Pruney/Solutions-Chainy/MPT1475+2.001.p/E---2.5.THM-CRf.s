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

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 431 expanded)
%              Number of clauses        :   25 ( 185 expanded)
%              Number of leaves         :    8 ( 106 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 837 expanded)
%              Number of equality atoms :   35 ( 256 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_lattice3,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_lattice3)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(d5_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_lattice3)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(involutiveness_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,k3_relset_1(X1,X2,X3)) = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_relset_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => k7_lattice3(k7_lattice3(X1)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t8_lattice3])).

fof(c_0_9,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | m1_subset_1(u1_orders_2(X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X14)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & k7_lattice3(k7_lattice3(esk1_0)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | m1_subset_1(k3_relset_1(X5,X6,X7),k1_zfmisc_1(k2_zfmisc_1(X6,X5))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | k7_lattice3(X19) = g1_orders_2(u1_struct_0(X19),k3_relset_1(u1_struct_0(X19),u1_struct_0(X19),u1_orders_2(X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( ( v1_orders_2(g1_orders_2(X12,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) )
      & ( l1_orders_2(g1_orders_2(X12,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k7_lattice3(X1) = g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X15 = X17
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) )
      & ( X16 = X18
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | ~ v1_orders_2(X11)
      | X11 = g1_orders_2(u1_struct_0(X11),u1_orders_2(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_21,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_13])).

cnf(c_0_24,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( v1_orders_2(k7_lattice3(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(k7_lattice3(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

fof(c_0_31,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | k3_relset_1(X8,X9,k3_relset_1(X8,X9,X10)) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_relset_1])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(k7_lattice3(esk1_0)) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( k3_relset_1(X2,X3,k3_relset_1(X2,X3,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = X1
    | k7_lattice3(esk1_0) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(esk1_0))) = k7_lattice3(esk1_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))) = u1_orders_2(esk1_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = u1_orders_2(k7_lattice3(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(esk1_0))) = u1_orders_2(esk1_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( k7_lattice3(k7_lattice3(esk1_0)) != g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_28]),c_0_33]),c_0_33]),c_0_33]),c_0_39]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:52:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___200_B02_F1_AE_CS_SP_PI_S0S
% 0.14/0.38  # and selection function SelectComplexG.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t8_lattice3, conjecture, ![X1]:(l1_orders_2(X1)=>k7_lattice3(k7_lattice3(X1))=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_lattice3)).
% 0.14/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.14/0.38  fof(dt_k3_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 0.14/0.38  fof(d5_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>k7_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_lattice3)).
% 0.14/0.38  fof(dt_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(v1_orders_2(g1_orders_2(X1,X2))&l1_orders_2(g1_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 0.14/0.38  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.14/0.38  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.14/0.38  fof(involutiveness_k3_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k3_relset_1(X1,X2,k3_relset_1(X1,X2,X3))=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_relset_1)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>k7_lattice3(k7_lattice3(X1))=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), inference(assume_negation,[status(cth)],[t8_lattice3])).
% 0.14/0.38  fof(c_0_9, plain, ![X14]:(~l1_orders_2(X14)|m1_subset_1(u1_orders_2(X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X14),u1_struct_0(X14))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, (l1_orders_2(esk1_0)&k7_lattice3(k7_lattice3(esk1_0))!=g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X5, X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|m1_subset_1(k3_relset_1(X5,X6,X7),k1_zfmisc_1(k2_zfmisc_1(X6,X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).
% 0.14/0.38  cnf(c_0_12, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_14, plain, ![X19]:(~l1_orders_2(X19)|k7_lattice3(X19)=g1_orders_2(u1_struct_0(X19),k3_relset_1(u1_struct_0(X19),u1_struct_0(X19),u1_orders_2(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_lattice3])])).
% 0.14/0.38  fof(c_0_15, plain, ![X12, X13]:((v1_orders_2(g1_orders_2(X12,X13))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))))&(l1_orders_2(g1_orders_2(X12,X13))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).
% 0.14/0.38  cnf(c_0_16, plain, (m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(u1_orders_2(esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_18, plain, (k7_lattice3(X1)=g1_orders_2(u1_struct_0(X1),k3_relset_1(u1_struct_0(X1),u1_struct_0(X1),u1_orders_2(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_19, plain, ![X15, X16, X17, X18]:((X15=X17|g1_orders_2(X15,X16)!=g1_orders_2(X17,X18)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))))&(X16=X18|g1_orders_2(X15,X16)!=g1_orders_2(X17,X18)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.14/0.38  fof(c_0_20, plain, ![X11]:(~l1_orders_2(X11)|(~v1_orders_2(X11)|X11=g1_orders_2(u1_struct_0(X11),u1_orders_2(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.14/0.38  cnf(c_0_21, plain, (v1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)))=k7_lattice3(esk1_0)), inference(spm,[status(thm)],[c_0_18, c_0_13])).
% 0.14/0.38  cnf(c_0_24, plain, (l1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_25, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_26, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (v1_orders_2(k7_lattice3(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (l1_orders_2(k7_lattice3(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_23])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (u1_struct_0(esk1_0)=X1|k7_lattice3(esk1_0)!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_23])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (g1_orders_2(u1_struct_0(k7_lattice3(esk1_0)),u1_orders_2(k7_lattice3(esk1_0)))=k7_lattice3(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.14/0.38  fof(c_0_31, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|k3_relset_1(X8,X9,k3_relset_1(X8,X9,X10))=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k3_relset_1])])).
% 0.14/0.38  cnf(c_0_32, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (u1_struct_0(k7_lattice3(esk1_0))=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  cnf(c_0_34, plain, (k3_relset_1(X2,X3,k3_relset_1(X2,X3,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))=X1|k7_lattice3(esk1_0)!=g1_orders_2(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_22]), c_0_23])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(esk1_0)))=k7_lattice3(esk1_0)), inference(rw,[status(thm)],[c_0_30, c_0_33])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0)))=u1_orders_2(esk1_0)), inference(spm,[status(thm)],[c_0_34, c_0_17])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(esk1_0))=u1_orders_2(k7_lattice3(esk1_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (k3_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_orders_2(k7_lattice3(esk1_0)))=u1_orders_2(esk1_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k7_lattice3(k7_lattice3(esk1_0))!=g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_28]), c_0_33]), c_0_33]), c_0_33]), c_0_39]), c_0_40]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 42
% 0.14/0.38  # Proof object clause steps            : 25
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 19
% 0.14/0.38  # Proof object clause conjectures      : 16
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 13
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 11
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 11
% 0.14/0.38  # Processed clauses                    : 38
% 0.14/0.38  # ...of these trivial                  : 1
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 36
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 2
% 0.14/0.38  # Backward-rewritten                   : 7
% 0.14/0.38  # Generated clauses                    : 32
% 0.14/0.38  # ...of the previous two non-trivial   : 33
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 30
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 27
% 0.14/0.38  #    Positive orientable unit clauses  : 13
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 13
% 0.14/0.38  # Current number of unprocessed clauses: 2
% 0.14/0.38  # ...number of literals in the above   : 2
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 9
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 7
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 7
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 17
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 7
% 0.14/0.38  # BW rewrite match successes           : 4
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1512
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.030 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
