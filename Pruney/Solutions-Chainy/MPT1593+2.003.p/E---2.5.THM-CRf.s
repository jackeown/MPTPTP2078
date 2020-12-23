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
% DateTime   : Thu Dec  3 11:15:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  83 expanded)
%              Number of clauses        :   21 (  40 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 144 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(t1_yellow_1,conjecture,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(c_0_6,plain,(
    ! [X12] :
      ( v1_orders_2(k2_yellow_1(X12))
      & l1_orders_2(k2_yellow_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_7,plain,(
    ! [X11] : k2_yellow_1(X11) = g1_orders_2(X11,k1_yellow_1(X11)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_9,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10] :
      ( ( X7 = X9
        | g1_orders_2(X7,X8) != g1_orders_2(X9,X10)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) )
      & ( X8 = X10
        | g1_orders_2(X7,X8) != g1_orders_2(X9,X10)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_13,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_10])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( u1_struct_0(k2_yellow_1(X1)) = X1
        & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t1_yellow_1])).

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

fof(c_0_19,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | m1_subset_1(u1_orders_2(X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X6)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_20,negated_conjecture,
    ( u1_struct_0(k2_yellow_1(esk1_0)) != esk1_0
    | u1_orders_2(k2_yellow_1(esk1_0)) != k1_yellow_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_21,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X3,X2)
    | ~ m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(k2_yellow_1(esk1_0)) != esk1_0
    | u1_orders_2(k2_yellow_1(esk1_0)) != k1_yellow_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = k1_yellow_1(X1)
    | ~ m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_27,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,X3)
    | ~ m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != esk1_0
    | u1_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != k1_yellow_1(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_10]),c_0_10])).

cnf(c_0_29,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = k1_yellow_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_30,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_32,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.38  # and selection function SelectNegativeLiterals.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.026 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.38  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.20/0.38  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.20/0.38  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.20/0.38  fof(t1_yellow_1, conjecture, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.20/0.38  fof(c_0_6, plain, ![X12]:(v1_orders_2(k2_yellow_1(X12))&l1_orders_2(k2_yellow_1(X12))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.38  fof(c_0_7, plain, ![X11]:k2_yellow_1(X11)=g1_orders_2(X11,k1_yellow_1(X11)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.20/0.38  fof(c_0_8, plain, ![X5]:(~l1_orders_2(X5)|(~v1_orders_2(X5)|X5=g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.20/0.38  cnf(c_0_9, plain, (v1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_10, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_11, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  fof(c_0_12, plain, ![X7, X8, X9, X10]:((X7=X9|g1_orders_2(X7,X8)!=g1_orders_2(X9,X10)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))))&(X8=X10|g1_orders_2(X7,X8)!=g1_orders_2(X9,X10)|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X7,X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.20/0.38  cnf(c_0_13, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, plain, (v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.38  cnf(c_0_15, plain, (l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_11, c_0_10])).
% 0.20/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1))), inference(assume_negation,[status(cth)],[t1_yellow_1])).
% 0.20/0.38  cnf(c_0_17, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_18, plain, (g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))))=g1_orders_2(X1,k1_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.20/0.38  fof(c_0_19, plain, ![X6]:(~l1_orders_2(X6)|m1_subset_1(u1_orders_2(X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X6))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.20/0.38  fof(c_0_20, negated_conjecture, (u1_struct_0(k2_yellow_1(esk1_0))!=esk1_0|u1_orders_2(k2_yellow_1(esk1_0))!=k1_yellow_1(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.20/0.38  cnf(c_0_21, plain, (u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))=X2|g1_orders_2(X1,k1_yellow_1(X1))!=g1_orders_2(X3,X2)|~m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.38  cnf(c_0_22, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.38  cnf(c_0_23, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (u1_struct_0(k2_yellow_1(esk1_0))!=esk1_0|u1_orders_2(k2_yellow_1(esk1_0))!=k1_yellow_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.38  cnf(c_0_25, plain, (u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))=k1_yellow_1(X1)|~m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))))), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_26, plain, (m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))))), inference(spm,[status(thm)],[c_0_22, c_0_15])).
% 0.20/0.38  cnf(c_0_27, plain, (u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))=X2|g1_orders_2(X1,k1_yellow_1(X1))!=g1_orders_2(X2,X3)|~m1_subset_1(u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))))), inference(spm,[status(thm)],[c_0_23, c_0_18])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))!=esk1_0|u1_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))!=k1_yellow_1(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_10]), c_0_10])).
% 0.20/0.38  cnf(c_0_29, plain, (u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))=k1_yellow_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26])])).
% 0.20/0.38  cnf(c_0_30, plain, (u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))=X2|g1_orders_2(X1,k1_yellow_1(X1))!=g1_orders_2(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_26])])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])])).
% 0.20/0.38  cnf(c_0_32, plain, (u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))=X1), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 34
% 0.20/0.38  # Proof object clause steps            : 21
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 7
% 0.20/0.38  # Proof object clause conjectures      : 4
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 8
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 6
% 0.20/0.38  # Proof object simplifying inferences  : 14
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 8
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 7
% 0.20/0.38  # Processed clauses                    : 29
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 0
% 0.20/0.38  # ...remaining for further processing  : 29
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 12
% 0.20/0.38  # Generated clauses                    : 25
% 0.20/0.38  # ...of the previous two non-trivial   : 30
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 17
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 8
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
% 0.20/0.38  # Current number of processed clauses  : 9
% 0.20/0.38  #    Positive orientable unit clauses  : 4
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 5
% 0.20/0.38  # Current number of unprocessed clauses: 14
% 0.20/0.38  # ...number of literals in the above   : 37
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 21
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 21
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 21
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 6
% 0.20/0.38  # BW rewrite match successes           : 6
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1178
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.027 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.031 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
