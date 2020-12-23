%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:40 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   32 (  92 expanded)
%              Number of clauses        :   19 (  43 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 259 expanded)
%              Number of equality atoms :   36 (  66 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_orders_2)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(t1_yellow_1,conjecture,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( ( v1_orders_2(g1_orders_2(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
      & ( l1_orders_2(g1_orders_2(X6,X7))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

fof(c_0_7,plain,(
    ! [X13] :
      ( v1_relat_2(k1_yellow_1(X13))
      & v4_relat_2(k1_yellow_1(X13))
      & v8_relat_2(k1_yellow_1(X13))
      & v1_partfun1(k1_yellow_1(X13),X13)
      & m1_subset_1(k1_yellow_1(X13),k1_zfmisc_1(k2_zfmisc_1(X13,X13))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | ~ v1_orders_2(X5)
      | X5 = g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_9,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_12,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X8 = X10
        | g1_orders_2(X8,X9) != g1_orders_2(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))) )
      & ( X9 = X11
        | g1_orders_2(X8,X9) != g1_orders_2(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_13,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( u1_struct_0(k2_yellow_1(X1)) = X1
        & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t1_yellow_1])).

cnf(c_0_19,plain,
    ( X1 = u1_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))
    | g1_orders_2(X3,X1) != g1_orders_2(X2,k1_yellow_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_20,negated_conjecture,
    ( u1_struct_0(k2_yellow_1(esk1_0)) != esk1_0
    | u1_orders_2(k2_yellow_1(esk1_0)) != k1_yellow_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X12] : k2_yellow_1(X12) = g1_orders_2(X12,k1_yellow_1(X12)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

cnf(c_0_22,plain,
    ( u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) = k1_yellow_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_10])])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(k2_yellow_1(esk1_0)) != esk1_0
    | u1_orders_2(k2_yellow_1(esk1_0)) != k1_yellow_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),k1_yellow_1(X1)) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != esk1_0
    | u1_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != k1_yellow_1(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_28,plain,
    ( X1 = u1_struct_0(g1_orders_2(X2,k1_yellow_1(X2)))
    | g1_orders_2(X1,X3) != g1_orders_2(X2,k1_yellow_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_22])])).

cnf(c_0_30,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]),c_0_10])])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 20:04:02 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S017A
% 0.11/0.35  # and selection function PSelectMinOptimalLit.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.027 s
% 0.11/0.35  # Presaturation interreduction done
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(dt_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>(v1_orders_2(g1_orders_2(X1,X2))&l1_orders_2(g1_orders_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_orders_2)).
% 0.11/0.35  fof(dt_k1_yellow_1, axiom, ![X1]:((((v1_relat_2(k1_yellow_1(X1))&v4_relat_2(k1_yellow_1(X1)))&v8_relat_2(k1_yellow_1(X1)))&v1_partfun1(k1_yellow_1(X1),X1))&m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 0.11/0.35  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.11/0.35  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.11/0.35  fof(t1_yellow_1, conjecture, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.11/0.35  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.11/0.35  fof(c_0_6, plain, ![X6, X7]:((v1_orders_2(g1_orders_2(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))&(l1_orders_2(g1_orders_2(X6,X7))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).
% 0.11/0.35  fof(c_0_7, plain, ![X13]:((((v1_relat_2(k1_yellow_1(X13))&v4_relat_2(k1_yellow_1(X13)))&v8_relat_2(k1_yellow_1(X13)))&v1_partfun1(k1_yellow_1(X13),X13))&m1_subset_1(k1_yellow_1(X13),k1_zfmisc_1(k2_zfmisc_1(X13,X13)))), inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).
% 0.11/0.35  fof(c_0_8, plain, ![X5]:(~l1_orders_2(X5)|(~v1_orders_2(X5)|X5=g1_orders_2(u1_struct_0(X5),u1_orders_2(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.11/0.35  cnf(c_0_9, plain, (v1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  cnf(c_0_10, plain, (m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.11/0.35  cnf(c_0_11, plain, (l1_orders_2(g1_orders_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.11/0.35  fof(c_0_12, plain, ![X8, X9, X10, X11]:((X8=X10|g1_orders_2(X8,X9)!=g1_orders_2(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))))&(X9=X11|g1_orders_2(X8,X9)!=g1_orders_2(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.11/0.35  cnf(c_0_13, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.35  cnf(c_0_14, plain, (v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.11/0.35  cnf(c_0_15, plain, (l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(spm,[status(thm)],[c_0_11, c_0_10])).
% 0.11/0.35  cnf(c_0_16, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  cnf(c_0_17, plain, (g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))))=g1_orders_2(X1,k1_yellow_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.11/0.35  fof(c_0_18, negated_conjecture, ~(![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1))), inference(assume_negation,[status(cth)],[t1_yellow_1])).
% 0.11/0.35  cnf(c_0_19, plain, (X1=u1_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))|g1_orders_2(X3,X1)!=g1_orders_2(X2,k1_yellow_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.11/0.35  fof(c_0_20, negated_conjecture, (u1_struct_0(k2_yellow_1(esk1_0))!=esk1_0|u1_orders_2(k2_yellow_1(esk1_0))!=k1_yellow_1(esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.11/0.35  fof(c_0_21, plain, ![X12]:k2_yellow_1(X12)=g1_orders_2(X12,k1_yellow_1(X12)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.11/0.35  cnf(c_0_22, plain, (u1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))=k1_yellow_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_10])])).
% 0.11/0.35  cnf(c_0_23, negated_conjecture, (u1_struct_0(k2_yellow_1(esk1_0))!=esk1_0|u1_orders_2(k2_yellow_1(esk1_0))!=k1_yellow_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.35  cnf(c_0_24, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.35  cnf(c_0_25, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  cnf(c_0_26, plain, (g1_orders_2(u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))),k1_yellow_1(X1))=g1_orders_2(X1,k1_yellow_1(X1))), inference(rw,[status(thm)],[c_0_17, c_0_22])).
% 0.11/0.35  cnf(c_0_27, negated_conjecture, (u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))!=esk1_0|u1_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))!=k1_yellow_1(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.11/0.35  cnf(c_0_28, plain, (X1=u1_struct_0(g1_orders_2(X2,k1_yellow_1(X2)))|g1_orders_2(X1,X3)!=g1_orders_2(X2,k1_yellow_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.11/0.35  cnf(c_0_29, negated_conjecture, (u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_22])])).
% 0.11/0.35  cnf(c_0_30, plain, (u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_28]), c_0_10])])).
% 0.11/0.35  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30])]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 32
% 0.11/0.35  # Proof object clause steps            : 19
% 0.11/0.35  # Proof object formula steps           : 13
% 0.11/0.35  # Proof object conjectures             : 7
% 0.11/0.35  # Proof object clause conjectures      : 4
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 8
% 0.11/0.35  # Proof object initial formulas used   : 6
% 0.11/0.35  # Proof object generating inferences   : 7
% 0.11/0.35  # Proof object simplifying inferences  : 13
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 6
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 12
% 0.11/0.35  # Removed in clause preprocessing      : 1
% 0.11/0.35  # Initial clauses in saturation        : 11
% 0.11/0.35  # Processed clauses                    : 34
% 0.11/0.35  # ...of these trivial                  : 1
% 0.11/0.35  # ...subsumed                          : 2
% 0.11/0.35  # ...remaining for further processing  : 31
% 0.11/0.35  # Other redundant clauses eliminated   : 0
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 0
% 0.11/0.35  # Backward-rewritten                   : 6
% 0.11/0.35  # Generated clauses                    : 23
% 0.11/0.35  # ...of the previous two non-trivial   : 20
% 0.11/0.35  # Contextual simplify-reflections      : 0
% 0.11/0.35  # Paramodulations                      : 19
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 4
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 14
% 0.11/0.35  #    Positive orientable unit clauses  : 9
% 0.11/0.35  #    Positive unorientable unit clauses: 0
% 0.11/0.35  #    Negative unit clauses             : 0
% 0.11/0.35  #    Non-unit-clauses                  : 5
% 0.11/0.35  # Current number of unprocessed clauses: 6
% 0.11/0.35  # ...number of literals in the above   : 18
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 18
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 12
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 12
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 2
% 0.11/0.35  # Unit Clause-clause subsumption calls : 0
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 6
% 0.11/0.35  # BW rewrite match successes           : 6
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 1148
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.028 s
% 0.11/0.35  # System time              : 0.003 s
% 0.11/0.35  # Total time               : 0.031 s
% 0.11/0.35  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
