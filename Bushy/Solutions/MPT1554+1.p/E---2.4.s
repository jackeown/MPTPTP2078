%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t32_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:40 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 894 expanded)
%              Number of clauses        :   37 ( 312 expanded)
%              Number of leaves         :    4 ( 214 expanded)
%              Depth                    :   11
%              Number of atoms          :  225 (8957 expanded)
%              Number of equality atoms :   34 (1355 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k1_yellow_0(X1,X3)
            <=> ( r2_lattice3(X1,X3,X2)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X3,X4)
                     => r1_orders_2(X1,X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t32_yellow_0.p',t32_yellow_0)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t32_yellow_0.p',t30_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t32_yellow_0.p',dt_k1_yellow_0)).

fof(t17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v3_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
          & r2_yellow_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t32_yellow_0.p',t17_yellow_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v3_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( X2 = k1_yellow_0(X1,X3)
              <=> ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_yellow_0])).

fof(c_0_5,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( r2_lattice3(X25,X27,X26)
        | X26 != k1_yellow_0(X25,X27)
        | ~ r1_yellow_0(X25,X27)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r2_lattice3(X25,X27,X28)
        | r1_orders_2(X25,X26,X28)
        | X26 != k1_yellow_0(X25,X27)
        | ~ r1_yellow_0(X25,X27)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( X26 = k1_yellow_0(X25,X29)
        | m1_subset_1(esk8_3(X25,X26,X29),u1_struct_0(X25))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_yellow_0(X25,X29)
        | m1_subset_1(esk8_3(X25,X26,X29),u1_struct_0(X25))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( X26 = k1_yellow_0(X25,X29)
        | r2_lattice3(X25,X29,esk8_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_yellow_0(X25,X29)
        | r2_lattice3(X25,X29,esk8_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( X26 = k1_yellow_0(X25,X29)
        | ~ r1_orders_2(X25,X26,esk8_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_yellow_0(X25,X29)
        | ~ r1_orders_2(X25,X26,esk8_3(X25,X26,X29))
        | ~ r2_lattice3(X25,X29,X26)
        | ~ m1_subset_1(X26,u1_struct_0(X25))
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_6,plain,(
    ! [X12,X13] :
      ( ~ l1_orders_2(X12)
      | m1_subset_1(k1_yellow_0(X12,X13),u1_struct_0(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_7,negated_conjecture,(
    ! [X9] :
      ( ~ v2_struct_0(esk1_0)
      & v5_orders_2(esk1_0)
      & v3_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k1_yellow_0(esk1_0,esk3_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k1_yellow_0(esk1_0,esk3_0) )
      & ( ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 != k1_yellow_0(esk1_0,esk3_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 = k1_yellow_0(esk1_0,esk3_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,esk2_0,X9)
        | esk2_0 = k1_yellow_0(esk1_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])])])).

fof(c_0_8,plain,(
    ! [X19,X20] :
      ( ( r1_yellow_0(X19,X20)
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v3_lattice3(X19)
        | ~ l1_orders_2(X19) )
      & ( r2_yellow_0(X19,X20)
        | v2_struct_0(X19)
        | ~ v5_orders_2(X19)
        | ~ v3_lattice3(X19)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t17_yellow_0])])])])])).

cnf(c_0_9,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v3_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( r1_yellow_0(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_18,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk8_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( r2_lattice3(esk1_0,X1,k1_yellow_0(esk1_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_13]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 = k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk8_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk8_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( k1_yellow_0(esk1_0,X1) = esk2_0
    | r2_lattice3(esk1_0,X1,esk8_3(esk1_0,esk2_0,X1))
    | ~ r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_13]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k1_yellow_0(esk1_0,X1) = esk2_0
    | m1_subset_1(esk8_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_13]),c_0_15])])).

cnf(c_0_27,negated_conjecture,
    ( k1_yellow_0(esk1_0,X1) = esk2_0
    | ~ r1_orders_2(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,X1))
    | ~ r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_13]),c_0_15])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,X1)
    | esk2_0 = k1_yellow_0(esk1_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk8_3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | m1_subset_1(esk8_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | ~ r1_orders_2(esk1_0,esk2_0,esk8_3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_33,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | k1_yellow_0(esk1_0,esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_25])])).

cnf(c_0_35,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | k1_yellow_0(esk1_0,esk3_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_25])])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) != esk2_0
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_25])])).

cnf(c_0_42,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,X1),esk4_0)
    | ~ r2_lattice3(esk1_0,X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_17]),c_0_13]),c_0_15])])).

cnf(c_0_43,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_35]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
