%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:08 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 (  41 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  124 ( 200 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   25 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_yellow_6,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X2)
                    & l1_waybel_0(X4,X2) )
                 => ( X4 = k3_yellow_6(X1,X2,X3)
                  <=> ( g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                      & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),u1_waybel_0(X2,X4),k8_funcop_1(u1_struct_0(X2),u1_struct_0(X4),X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_yellow_6)).

fof(dt_k3_yellow_6,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)
        & l1_waybel_0(k3_yellow_6(X1,X2,X3),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_6)).

fof(t13_yellow_6,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => u1_struct_0(k3_yellow_6(X1,X2,X3)) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_6)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13] :
      ( ( g1_orders_2(u1_struct_0(X13),u1_orders_2(X13)) = g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))
        | X13 != k3_yellow_6(X10,X11,X12)
        | ~ v6_waybel_0(X13,X11)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | ~ l1_orders_2(X10) )
      & ( r2_funct_2(u1_struct_0(X13),u1_struct_0(X11),u1_waybel_0(X11,X13),k8_funcop_1(u1_struct_0(X11),u1_struct_0(X13),X12))
        | X13 != k3_yellow_6(X10,X11,X12)
        | ~ v6_waybel_0(X13,X11)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | ~ l1_orders_2(X10) )
      & ( g1_orders_2(u1_struct_0(X13),u1_orders_2(X13)) != g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))
        | ~ r2_funct_2(u1_struct_0(X13),u1_struct_0(X11),u1_waybel_0(X11,X13),k8_funcop_1(u1_struct_0(X11),u1_struct_0(X13),X12))
        | X13 = k3_yellow_6(X10,X11,X12)
        | ~ v6_waybel_0(X13,X11)
        | ~ l1_waybel_0(X13,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ l1_struct_0(X11)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_yellow_6])])])])])).

fof(c_0_6,plain,(
    ! [X14,X15,X16] :
      ( ( v6_waybel_0(k3_yellow_6(X14,X15,X16),X15)
        | ~ l1_orders_2(X14)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15)) )
      & ( l1_waybel_0(k3_yellow_6(X14,X15,X16),X15)
        | ~ l1_orders_2(X14)
        | v2_struct_0(X15)
        | ~ l1_struct_0(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow_6])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => u1_struct_0(k3_yellow_6(X1,X2,X3)) = u1_struct_0(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_6])).

fof(c_0_8,plain,(
    ! [X6,X7,X8,X9] :
      ( ( X6 = X8
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
      & ( X7 = X9
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_9,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | m1_subset_1(u1_orders_2(X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X5)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_10,plain,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | v2_struct_0(X3)
    | X1 != k3_yellow_6(X2,X3,X4)
    | ~ v6_waybel_0(X1,X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_struct_0(X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( l1_waybel_0(k3_yellow_6(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0)) != u1_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(X1,X2,X3)),u1_orders_2(k3_yellow_6(X1,X2,X3))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0)),u1_orders_2(k3_yellow_6(X1,esk2_0,esk3_0))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(k3_yellow_6(X2,esk2_0,esk3_0))
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0)) != u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0)) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:15:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(d7_yellow_6, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:((v6_waybel_0(X4,X2)&l1_waybel_0(X4,X2))=>(X4=k3_yellow_6(X1,X2,X3)<=>(g1_orders_2(u1_struct_0(X4),u1_orders_2(X4))=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))&r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),u1_waybel_0(X2,X4),k8_funcop_1(u1_struct_0(X2),u1_struct_0(X4),X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_yellow_6)).
% 0.12/0.38  fof(dt_k3_yellow_6, axiom, ![X1, X2, X3]:((((l1_orders_2(X1)&~(v2_struct_0(X2)))&l1_struct_0(X2))&m1_subset_1(X3,u1_struct_0(X2)))=>(v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)&l1_waybel_0(k3_yellow_6(X1,X2,X3),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_6)).
% 0.12/0.38  fof(t13_yellow_6, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>u1_struct_0(k3_yellow_6(X1,X2,X3))=u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_6)).
% 0.12/0.38  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.12/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.12/0.38  fof(c_0_5, plain, ![X10, X11, X12, X13]:(((g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))=g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))|X13!=k3_yellow_6(X10,X11,X12)|(~v6_waybel_0(X13,X11)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_struct_0(X11))|~l1_orders_2(X10))&(r2_funct_2(u1_struct_0(X13),u1_struct_0(X11),u1_waybel_0(X11,X13),k8_funcop_1(u1_struct_0(X11),u1_struct_0(X13),X12))|X13!=k3_yellow_6(X10,X11,X12)|(~v6_waybel_0(X13,X11)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_struct_0(X11))|~l1_orders_2(X10)))&(g1_orders_2(u1_struct_0(X13),u1_orders_2(X13))!=g1_orders_2(u1_struct_0(X10),u1_orders_2(X10))|~r2_funct_2(u1_struct_0(X13),u1_struct_0(X11),u1_waybel_0(X11,X13),k8_funcop_1(u1_struct_0(X11),u1_struct_0(X13),X12))|X13=k3_yellow_6(X10,X11,X12)|(~v6_waybel_0(X13,X11)|~l1_waybel_0(X13,X11))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~l1_struct_0(X11))|~l1_orders_2(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_yellow_6])])])])])).
% 0.12/0.38  fof(c_0_6, plain, ![X14, X15, X16]:((v6_waybel_0(k3_yellow_6(X14,X15,X16),X15)|(~l1_orders_2(X14)|v2_struct_0(X15)|~l1_struct_0(X15)|~m1_subset_1(X16,u1_struct_0(X15))))&(l1_waybel_0(k3_yellow_6(X14,X15,X16),X15)|(~l1_orders_2(X14)|v2_struct_0(X15)|~l1_struct_0(X15)|~m1_subset_1(X16,u1_struct_0(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow_6])])])])).
% 0.12/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>u1_struct_0(k3_yellow_6(X1,X2,X3))=u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t13_yellow_6])).
% 0.12/0.38  fof(c_0_8, plain, ![X6, X7, X8, X9]:((X6=X8|g1_orders_2(X6,X7)!=g1_orders_2(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))&(X7=X9|g1_orders_2(X6,X7)!=g1_orders_2(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.12/0.38  fof(c_0_9, plain, ![X5]:(~l1_orders_2(X5)|m1_subset_1(u1_orders_2(X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X5))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.12/0.38  cnf(c_0_10, plain, (g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))|v2_struct_0(X3)|X1!=k3_yellow_6(X2,X3,X4)|~v6_waybel_0(X1,X3)|~l1_waybel_0(X1,X3)|~m1_subset_1(X4,u1_struct_0(X3))|~l1_struct_0(X3)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.38  cnf(c_0_11, plain, (v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)|v2_struct_0(X2)|~l1_orders_2(X1)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  cnf(c_0_12, plain, (l1_waybel_0(k3_yellow_6(X1,X2,X3),X2)|v2_struct_0(X2)|~l1_orders_2(X1)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.38  fof(c_0_13, negated_conjecture, (l1_orders_2(esk1_0)&((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0))!=u1_struct_0(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.12/0.38  cnf(c_0_14, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_15, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_16, plain, (g1_orders_2(u1_struct_0(k3_yellow_6(X1,X2,X3)),u1_orders_2(k3_yellow_6(X1,X2,X3)))=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|v2_struct_0(X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11]), c_0_12])).
% 0.12/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_18, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_20, plain, (u1_struct_0(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X2,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (g1_orders_2(u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0)),u1_orders_2(k3_yellow_6(X1,esk2_0,esk3_0)))=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.38  cnf(c_0_22, negated_conjecture, (u1_struct_0(X1)=u1_struct_0(k3_yellow_6(X2,esk2_0,esk3_0))|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.38  cnf(c_0_23, negated_conjecture, (u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0))!=u1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0))=u1_struct_0(X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 27
% 0.12/0.38  # Proof object clause steps            : 16
% 0.12/0.38  # Proof object formula steps           : 11
% 0.12/0.38  # Proof object conjectures             : 12
% 0.12/0.38  # Proof object clause conjectures      : 9
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 10
% 0.12/0.38  # Proof object initial formulas used   : 5
% 0.12/0.38  # Proof object generating inferences   : 5
% 0.12/0.38  # Proof object simplifying inferences  : 8
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 5
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 13
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 13
% 0.12/0.38  # Processed clauses                    : 51
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 2
% 0.12/0.38  # ...remaining for further processing  : 49
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 0
% 0.12/0.38  # Generated clauses                    : 69
% 0.12/0.38  # ...of the previous two non-trivial   : 62
% 0.12/0.38  # Contextual simplify-reflections      : 4
% 0.12/0.38  # Paramodulations                      : 60
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 9
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
% 0.12/0.38  # Current number of processed clauses  : 33
% 0.12/0.38  #    Positive orientable unit clauses  : 5
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 3
% 0.12/0.38  #    Non-unit-clauses                  : 25
% 0.12/0.38  # Current number of unprocessed clauses: 24
% 0.12/0.38  # ...number of literals in the above   : 97
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 14
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 266
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 103
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.12/0.38  # Unit Clause-clause subsumption calls : 14
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 0
% 0.12/0.38  # BW rewrite match successes           : 0
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 3301
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.034 s
% 0.12/0.38  # System time              : 0.001 s
% 0.12/0.38  # Total time               : 0.035 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
