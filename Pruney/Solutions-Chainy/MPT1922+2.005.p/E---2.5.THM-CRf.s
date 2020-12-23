%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:10 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  83 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 619 expanded)
%              Number of equality atoms :   17 ( 103 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( X5 = X3
                              & X6 = X4
                              & r1_orders_2(X2,X5,X6) )
                           => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

fof(t20_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X3))
                             => ( ( X4 = X6
                                  & X5 = X7
                                  & r1_orders_2(X3,X6,X7) )
                               => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_yellow_6)).

fof(d8_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( l1_waybel_0(X3,X1)
             => ( m1_yellow_6(X3,X1,X2)
              <=> ( m1_yellow_0(X3,X2)
                  & u1_waybel_0(X1,X3) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ~ l1_orders_2(X8)
      | ~ m1_yellow_0(X9,X8)
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X13,u1_struct_0(X9))
      | X12 != X10
      | X13 != X11
      | ~ r1_orders_2(X9,X12,X13)
      | r1_orders_2(X8,X10,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_yellow_0])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_waybel_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_6(X3,X1,X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X4 = X6
                                    & X5 = X7
                                    & r1_orders_2(X3,X6,X7) )
                                 => r1_orders_2(X2,X4,X5) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_yellow_6])).

cnf(c_0_7,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | X5 != X3
    | X6 != X4
    | ~ r1_orders_2(X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_yellow_6(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk4_0 = esk6_0
    & esk5_0 = esk7_0
    & r1_orders_2(esk3_0,esk6_0,esk7_0)
    & ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X16,X17,X18] :
      ( ( m1_yellow_0(X18,X17)
        | ~ m1_yellow_6(X18,X16,X17)
        | ~ l1_waybel_0(X18,X16)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_struct_0(X16) )
      & ( u1_waybel_0(X16,X18) = k2_partfun1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17),u1_struct_0(X18))
        | ~ m1_yellow_6(X18,X16,X17)
        | ~ l1_waybel_0(X18,X16)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_struct_0(X16) )
      & ( ~ m1_yellow_0(X18,X17)
        | u1_waybel_0(X16,X18) != k2_partfun1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17),u1_struct_0(X18))
        | m1_yellow_6(X18,X16,X17)
        | ~ l1_waybel_0(X18,X16)
        | ~ l1_waybel_0(X17,X16)
        | ~ l1_struct_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

fof(c_0_10,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_struct_0(X19)
      | ~ l1_waybel_0(X20,X19)
      | ~ m1_yellow_6(X21,X19,X20)
      | l1_waybel_0(X21,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

cnf(c_0_11,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X4,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(X4,X1)
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_orders_2(esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( esk4_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X14,X15] :
      ( ~ l1_struct_0(X14)
      | ~ l1_waybel_0(X15,X14)
      | l1_orders_2(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_17,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(X1,X2,esk7_0)
    | ~ r1_orders_2(esk3_0,X2,esk7_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(esk3_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_22,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( esk5_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( m1_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(X1,esk4_0,esk7_0)
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk4_0,u1_struct_0(X1))
    | ~ m1_yellow_0(esk3_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_31,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_orders_2(esk2_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_24])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t60_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(((X5=X3&X6=X4)&r1_orders_2(X2,X5,X6))=>r1_orders_2(X1,X3,X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_yellow_0)).
% 0.21/0.38  fof(t20_yellow_6, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X3,X6,X7))=>r1_orders_2(X2,X4,X5))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_yellow_6)).
% 0.21/0.38  fof(d8_yellow_6, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(l1_waybel_0(X3,X1)=>(m1_yellow_6(X3,X1,X2)<=>(m1_yellow_0(X3,X2)&u1_waybel_0(X1,X3)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_6)).
% 0.21/0.38  fof(dt_m1_yellow_6, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>![X3]:(m1_yellow_6(X3,X1,X2)=>l1_waybel_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 0.21/0.38  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.21/0.38  fof(c_0_5, plain, ![X8, X9, X10, X11, X12, X13]:(~l1_orders_2(X8)|(~m1_yellow_0(X9,X8)|(~m1_subset_1(X10,u1_struct_0(X8))|(~m1_subset_1(X11,u1_struct_0(X8))|(~m1_subset_1(X12,u1_struct_0(X9))|(~m1_subset_1(X13,u1_struct_0(X9))|(X12!=X10|X13!=X11|~r1_orders_2(X9,X12,X13)|r1_orders_2(X8,X10,X11)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_yellow_0])])])).
% 0.21/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X4=X6&X5=X7)&r1_orders_2(X3,X6,X7))=>r1_orders_2(X2,X4,X5)))))))))), inference(assume_negation,[status(cth)],[t20_yellow_6])).
% 0.21/0.38  cnf(c_0_7, plain, (r1_orders_2(X1,X3,X4)|~l1_orders_2(X1)|~m1_yellow_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X2))|X5!=X3|X6!=X4|~r1_orders_2(X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.38  fof(c_0_8, negated_conjecture, (l1_struct_0(esk1_0)&(l1_waybel_0(esk2_0,esk1_0)&(m1_yellow_6(esk3_0,esk1_0,esk2_0)&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(esk2_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&(((esk4_0=esk6_0&esk5_0=esk7_0)&r1_orders_2(esk3_0,esk6_0,esk7_0))&~r1_orders_2(esk2_0,esk4_0,esk5_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.21/0.38  fof(c_0_9, plain, ![X16, X17, X18]:(((m1_yellow_0(X18,X17)|~m1_yellow_6(X18,X16,X17)|~l1_waybel_0(X18,X16)|~l1_waybel_0(X17,X16)|~l1_struct_0(X16))&(u1_waybel_0(X16,X18)=k2_partfun1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17),u1_struct_0(X18))|~m1_yellow_6(X18,X16,X17)|~l1_waybel_0(X18,X16)|~l1_waybel_0(X17,X16)|~l1_struct_0(X16)))&(~m1_yellow_0(X18,X17)|u1_waybel_0(X16,X18)!=k2_partfun1(u1_struct_0(X17),u1_struct_0(X16),u1_waybel_0(X16,X17),u1_struct_0(X18))|m1_yellow_6(X18,X16,X17)|~l1_waybel_0(X18,X16)|~l1_waybel_0(X17,X16)|~l1_struct_0(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).
% 0.21/0.38  fof(c_0_10, plain, ![X19, X20, X21]:(~l1_struct_0(X19)|~l1_waybel_0(X20,X19)|(~m1_yellow_6(X21,X19,X20)|l1_waybel_0(X21,X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).
% 0.21/0.38  cnf(c_0_11, plain, (r1_orders_2(X1,X2,X3)|~r1_orders_2(X4,X2,X3)|~m1_subset_1(X3,u1_struct_0(X4))|~m1_subset_1(X2,u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_yellow_0(X4,X1)|~l1_orders_2(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).
% 0.21/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_13, negated_conjecture, (r1_orders_2(esk3_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_14, negated_conjecture, (esk4_0=esk6_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  fof(c_0_16, plain, ![X14, X15]:(~l1_struct_0(X14)|(~l1_waybel_0(X15,X14)|l1_orders_2(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.21/0.38  cnf(c_0_17, plain, (m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_18, plain, (l1_waybel_0(X3,X1)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_yellow_6(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_19, negated_conjecture, (r1_orders_2(X1,X2,esk7_0)|~r1_orders_2(esk3_0,X2,esk7_0)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_yellow_0(esk3_0,X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.38  cnf(c_0_20, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.21/0.38  cnf(c_0_22, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (l1_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_24, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (esk5_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (~r1_orders_2(esk2_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_28, plain, (m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (m1_yellow_6(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (r1_orders_2(X1,esk4_0,esk7_0)|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_subset_1(esk4_0,u1_struct_0(X1))|~m1_yellow_0(esk3_0,X1)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (l1_orders_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_34, negated_conjecture, (~r1_orders_2(esk2_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (m1_yellow_0(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23]), c_0_24])])).
% 0.21/0.38  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])]), c_0_34]), c_0_35])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 37
% 0.21/0.38  # Proof object clause steps            : 26
% 0.21/0.38  # Proof object formula steps           : 11
% 0.21/0.38  # Proof object conjectures             : 23
% 0.21/0.38  # Proof object clause conjectures      : 20
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 15
% 0.21/0.38  # Proof object initial formulas used   : 5
% 0.21/0.38  # Proof object generating inferences   : 5
% 0.21/0.38  # Proof object simplifying inferences  : 20
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 5
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 17
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 17
% 0.21/0.38  # Processed clauses                    : 41
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 40
% 0.21/0.38  # Other redundant clauses eliminated   : 2
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 0
% 0.21/0.38  # Generated clauses                    : 12
% 0.21/0.38  # ...of the previous two non-trivial   : 11
% 0.21/0.38  # Contextual simplify-reflections      : 2
% 0.21/0.38  # Paramodulations                      : 11
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 2
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 22
% 0.21/0.38  #    Positive orientable unit clauses  : 14
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 7
% 0.21/0.38  # Current number of unprocessed clauses: 4
% 0.21/0.38  # ...number of literals in the above   : 25
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 17
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 39
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 7
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.21/0.38  # Unit Clause-clause subsumption calls : 0
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 0
% 0.21/0.38  # BW rewrite match successes           : 0
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 1702
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.030 s
% 0.21/0.38  # System time              : 0.002 s
% 0.21/0.38  # Total time               : 0.032 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
