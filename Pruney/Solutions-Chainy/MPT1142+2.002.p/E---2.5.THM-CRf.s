%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:31 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (2127 expanded)
%              Number of clauses        :   36 ( 723 expanded)
%              Number of leaves         :    4 ( 502 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 (18774 expanded)
%              Number of equality atoms :   19 ( 406 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_orders_2,conjecture,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( ( r2_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X3,X4) )
                      | ( r1_orders_2(X1,X2,X3)
                        & r2_orders_2(X1,X3,X4) ) )
                   => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(t28_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( r2_orders_2(X1,X2,X3)
                  & r2_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( ( r2_orders_2(X1,X2,X3)
                          & r1_orders_2(X1,X3,X4) )
                        | ( r1_orders_2(X1,X2,X3)
                          & r2_orders_2(X1,X3,X4) ) )
                     => r2_orders_2(X1,X2,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_orders_2])).

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( ( r1_orders_2(X5,X6,X7)
        | ~ r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( X6 != X7
        | ~ r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | X6 = X7
        | r2_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

fof(c_0_6,negated_conjecture,
    ( v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r2_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | r2_orders_2(esk1_0,esk2_0,esk3_0) )
    & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ( r2_orders_2(esk1_0,esk3_0,esk4_0)
      | r1_orders_2(esk1_0,esk3_0,esk4_0) )
    & ~ r2_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10,X11] :
      ( ~ v4_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ r1_orders_2(X8,X9,X10)
      | ~ r1_orders_2(X8,X10,X11)
      | r1_orders_2(X8,X9,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_8,plain,
    ( X2 = X3
    | r2_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])])).

cnf(c_0_14,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,X2,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_12]),c_0_10])])).

cnf(c_0_15,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,X2,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk4_0)
    | ~ r2_orders_2(esk1_0,X1,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_9]),c_0_10])])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r2_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10])])).

cnf(c_0_20,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ r2_orders_2(esk1_0,X2,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_26,plain,(
    ! [X12,X13,X14] :
      ( ~ v5_orders_2(X12)
      | ~ l1_orders_2(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ r2_orders_2(X12,X13,X14)
      | ~ r2_orders_2(X12,X14,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_orders_2])])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = esk4_0
    | r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_0)
    | ~ r2_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_19]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( esk4_0 = esk2_0
    | r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_16])]),c_0_23]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk4_0 = esk2_0
    | r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_25]),c_0_22]),c_0_16])]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_orders_2(esk1_0,esk3_0,esk4_0)
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
    ( ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X3)
    | ~ r2_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( X1 = esk3_0
    | r2_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_16]),c_0_10])])).

cnf(c_0_34,negated_conjecture,
    ( esk4_0 = esk2_0
    | X1 = esk4_0
    | r2_orders_2(esk1_0,X1,esk4_0)
    | ~ r2_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk4_0 = esk2_0
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_16])]),c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,X1,X2)
    | ~ r2_orders_2(esk1_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_10])])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 = esk3_0
    | r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_22])])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_34]),c_0_22])]),c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_orders_2(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_24]),c_0_16])])).

cnf(c_0_40,negated_conjecture,
    ( esk2_0 = esk3_0
    | ~ r2_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22]),c_0_16])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_38]),c_0_38]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_38]),c_0_42]),c_0_42])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S021N
% 0.20/0.41  # and selection function PSelectAllCondOptimalLit.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.027 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t32_orders_2, conjecture, ![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))|(r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4)))=>r2_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_orders_2)).
% 0.20/0.41  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 0.20/0.41  fof(t26_orders_2, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 0.20/0.41  fof(t28_orders_2, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 0.20/0.41  fof(c_0_4, negated_conjecture, ~(![X1]:(((v4_orders_2(X1)&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))|(r1_orders_2(X1,X2,X3)&r2_orders_2(X1,X3,X4)))=>r2_orders_2(X1,X2,X4))))))), inference(assume_negation,[status(cth)],[t32_orders_2])).
% 0.20/0.41  fof(c_0_5, plain, ![X5, X6, X7]:(((r1_orders_2(X5,X6,X7)|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))&(X6!=X7|~r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5)))&(~r1_orders_2(X5,X6,X7)|X6=X7|r2_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.20/0.41  fof(c_0_6, negated_conjecture, (((v4_orders_2(esk1_0)&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&(m1_subset_1(esk3_0,u1_struct_0(esk1_0))&(m1_subset_1(esk4_0,u1_struct_0(esk1_0))&((((r1_orders_2(esk1_0,esk2_0,esk3_0)|r2_orders_2(esk1_0,esk2_0,esk3_0))&(r2_orders_2(esk1_0,esk3_0,esk4_0)|r2_orders_2(esk1_0,esk2_0,esk3_0)))&((r1_orders_2(esk1_0,esk2_0,esk3_0)|r1_orders_2(esk1_0,esk3_0,esk4_0))&(r2_orders_2(esk1_0,esk3_0,esk4_0)|r1_orders_2(esk1_0,esk3_0,esk4_0))))&~r2_orders_2(esk1_0,esk2_0,esk4_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.20/0.41  fof(c_0_7, plain, ![X8, X9, X10, X11]:(~v4_orders_2(X8)|~l1_orders_2(X8)|(~m1_subset_1(X9,u1_struct_0(X8))|(~m1_subset_1(X10,u1_struct_0(X8))|(~m1_subset_1(X11,u1_struct_0(X8))|(~r1_orders_2(X8,X9,X10)|~r1_orders_2(X8,X10,X11)|r1_orders_2(X8,X9,X11)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).
% 0.20/0.41  cnf(c_0_8, plain, (X2=X3|r2_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.41  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_11, plain, (r1_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.41  cnf(c_0_12, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_13, negated_conjecture, (X1=esk4_0|r2_orders_2(esk1_0,X1,esk4_0)|~r1_orders_2(esk1_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10])])).
% 0.20/0.41  cnf(c_0_14, negated_conjecture, (r1_orders_2(esk1_0,X1,esk4_0)|~r1_orders_2(esk1_0,X2,esk4_0)|~r1_orders_2(esk1_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_9]), c_0_12]), c_0_10])])).
% 0.20/0.41  cnf(c_0_15, plain, (r1_orders_2(X1,X2,X3)|~r2_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_17, negated_conjecture, (X1=esk4_0|r2_orders_2(esk1_0,X1,esk4_0)|~r1_orders_2(esk1_0,X2,esk4_0)|~r1_orders_2(esk1_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.41  cnf(c_0_18, negated_conjecture, (r1_orders_2(esk1_0,X1,esk4_0)|~r2_orders_2(esk1_0,X1,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_9]), c_0_10])])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (r1_orders_2(esk1_0,X1,esk3_0)|~r2_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_10])])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (X1=esk4_0|r2_orders_2(esk1_0,X1,esk4_0)|~r1_orders_2(esk1_0,X1,X2)|~r2_orders_2(esk1_0,X2,esk4_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,esk3_0)|r1_orders_2(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (~r2_orders_2(esk1_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (r2_orders_2(esk1_0,esk3_0,esk4_0)|r1_orders_2(esk1_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (r1_orders_2(esk1_0,esk2_0,esk3_0)|r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  fof(c_0_26, plain, ![X12, X13, X14]:(~v5_orders_2(X12)|~l1_orders_2(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|(~r2_orders_2(X12,X13,X14)|~r2_orders_2(X12,X14,X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_orders_2])])])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (X1=esk4_0|r2_orders_2(esk1_0,X1,esk4_0)|~r1_orders_2(esk1_0,esk3_0,esk4_0)|~r2_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_19]), c_0_16])])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (esk4_0=esk2_0|r1_orders_2(esk1_0,esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_16])]), c_0_23]), c_0_24])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (esk4_0=esk2_0|r2_orders_2(esk1_0,esk2_0,esk3_0)|~r1_orders_2(esk1_0,esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_25]), c_0_22]), c_0_16])]), c_0_23])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (r2_orders_2(esk1_0,esk3_0,esk4_0)|r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_31, plain, (~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_orders_2(X1,X2,X3)|~r2_orders_2(X1,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (X1=esk3_0|r2_orders_2(esk1_0,X1,esk3_0)|~r1_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_16]), c_0_10])])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (esk4_0=esk2_0|X1=esk4_0|r2_orders_2(esk1_0,X1,esk4_0)|~r2_orders_2(esk1_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (esk4_0=esk2_0|r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_18]), c_0_16])]), c_0_30])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (~r2_orders_2(esk1_0,X1,X2)|~r2_orders_2(esk1_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X2,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_10])])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (esk2_0=esk3_0|r2_orders_2(esk1_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_25]), c_0_22])])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (esk4_0=esk2_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_34]), c_0_22])]), c_0_35])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (esk4_0=esk3_0|r2_orders_2(esk1_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_24]), c_0_16])])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (esk2_0=esk3_0|~r2_orders_2(esk1_0,esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_22]), c_0_16])])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (~r2_orders_2(esk1_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[c_0_23, c_0_38])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (esk2_0=esk3_0), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_38]), c_0_38]), c_0_40])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (~r2_orders_2(esk1_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_38]), c_0_42]), c_0_42])]), c_0_43]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 45
% 0.20/0.41  # Proof object clause steps            : 36
% 0.20/0.41  # Proof object formula steps           : 9
% 0.20/0.41  # Proof object conjectures             : 35
% 0.20/0.41  # Proof object clause conjectures      : 32
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 15
% 0.20/0.41  # Proof object initial formulas used   : 4
% 0.20/0.41  # Proof object generating inferences   : 17
% 0.20/0.41  # Proof object simplifying inferences  : 48
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 4
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 16
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 16
% 0.20/0.41  # Processed clauses                    : 279
% 0.20/0.41  # ...of these trivial                  : 1
% 0.20/0.41  # ...subsumed                          : 146
% 0.20/0.41  # ...remaining for further processing  : 131
% 0.20/0.41  # Other redundant clauses eliminated   : 1
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 15
% 0.20/0.41  # Backward-rewritten                   : 78
% 0.20/0.41  # Generated clauses                    : 1429
% 0.20/0.41  # ...of the previous two non-trivial   : 1345
% 0.20/0.41  # Contextual simplify-reflections      : 15
% 0.20/0.41  # Paramodulations                      : 1428
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 1
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 21
% 0.20/0.41  #    Positive orientable unit clauses  : 7
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 13
% 0.20/0.41  # Current number of unprocessed clauses: 1040
% 0.20/0.41  # ...number of literals in the above   : 7454
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 109
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 1515
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 500
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 165
% 0.20/0.41  # Unit Clause-clause subsumption calls : 20
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 2
% 0.20/0.41  # BW rewrite match successes           : 2
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 37853
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.058 s
% 0.20/0.41  # System time              : 0.009 s
% 0.20/0.41  # Total time               : 0.067 s
% 0.20/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
