%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t45_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:43 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  65 expanded)
%              Number of clauses        :   17 (  22 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :  156 ( 341 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t45_yellow_0.p',t31_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t45_yellow_0.p',dt_k2_yellow_0)).

fof(t45_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t45_yellow_0.p',t45_yellow_0)).

fof(t43_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r2_yellow_0(X1,k1_xboole_0)
        & r1_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t45_yellow_0.p',t43_yellow_0)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t45_yellow_0.p',t6_yellow_0)).

fof(d12_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t45_yellow_0.p',d12_yellow_0)).

fof(c_0_6,plain,(
    ! [X22,X23,X24,X25,X26] :
      ( ( r1_lattice3(X22,X24,X23)
        | X23 != k2_yellow_0(X22,X24)
        | ~ r2_yellow_0(X22,X24)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r1_lattice3(X22,X24,X25)
        | r1_orders_2(X22,X25,X23)
        | X23 != k2_yellow_0(X22,X24)
        | ~ r2_yellow_0(X22,X24)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X23 = k2_yellow_0(X22,X26)
        | m1_subset_1(esk6_3(X22,X23,X26),u1_struct_0(X22))
        | ~ r1_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_yellow_0(X22,X26)
        | m1_subset_1(esk6_3(X22,X23,X26),u1_struct_0(X22))
        | ~ r1_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X23 = k2_yellow_0(X22,X26)
        | r1_lattice3(X22,X26,esk6_3(X22,X23,X26))
        | ~ r1_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_yellow_0(X22,X26)
        | r1_lattice3(X22,X26,esk6_3(X22,X23,X26))
        | ~ r1_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( X23 = k2_yellow_0(X22,X26)
        | ~ r1_orders_2(X22,esk6_3(X22,X23,X26),X23)
        | ~ r1_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_yellow_0(X22,X26)
        | ~ r1_orders_2(X22,esk6_3(X22,X23,X26),X23)
        | ~ r1_lattice3(X22,X26,X23)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

fof(c_0_7,plain,(
    ! [X10,X11] :
      ( ~ l1_orders_2(X10)
      | m1_subset_1(k2_yellow_0(X10,X11),u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v5_orders_2(X1)
          & v2_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,X2,k4_yellow_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t45_yellow_0])).

cnf(c_0_9,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v5_orders_2(esk1_0)
    & v2_yellow_0(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ r1_orders_2(esk1_0,esk2_0,k4_yellow_0(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_12,plain,(
    ! [X28] :
      ( ( r2_yellow_0(X28,k1_xboole_0)
        | v2_struct_0(X28)
        | ~ v5_orders_2(X28)
        | ~ v2_yellow_0(X28)
        | ~ l1_orders_2(X28) )
      & ( r1_yellow_0(X28,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v5_orders_2(X28)
        | ~ v2_yellow_0(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t43_yellow_0])])])])).

fof(c_0_13,plain,(
    ! [X30,X31] :
      ( ( r2_lattice3(X30,k1_xboole_0,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) )
      & ( r1_lattice3(X30,k1_xboole_0,X31)
        | ~ m1_subset_1(X31,u1_struct_0(X30))
        | ~ l1_orders_2(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

fof(c_0_14,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | k4_yellow_0(X9) = k2_yellow_0(X9,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_yellow_0])])).

cnf(c_0_15,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r1_lattice3(X1,X3,X2)
    | ~ r2_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( r2_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v2_yellow_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,k4_yellow_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( k4_yellow_0(X1) = k2_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,k2_yellow_0(esk1_0,X1))
    | ~ r1_lattice3(esk1_0,X1,esk2_0)
    | ~ r2_yellow_0(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_26,negated_conjecture,
    ( r2_yellow_0(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17]),c_0_21]),c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( r1_lattice3(esk1_0,k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17])])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,k2_yellow_0(esk1_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
