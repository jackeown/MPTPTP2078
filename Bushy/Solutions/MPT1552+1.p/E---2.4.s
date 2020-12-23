%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t30_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:40 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   69 (67933 expanded)
%              Number of clauses        :   60 (22293 expanded)
%              Number of leaves         :    4 (16381 expanded)
%              Depth                    :   27
%              Number of atoms          :  342 (1311567 expanded)
%              Number of equality atoms :   49 (176214 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   57 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t30_yellow_0,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t30_yellow_0.p',t30_yellow_0)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t30_yellow_0.p',d9_yellow_0)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t30_yellow_0.p',t15_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t30_yellow_0.p',dt_k1_yellow_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
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
    inference(assume_negation,[status(cth)],[t30_yellow_0])).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r2_lattice3(X10,X11,X12)
        | X12 != k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X13)
        | r1_orders_2(X10,X12,X13)
        | X12 != k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk5_3(X10,X11,X12),u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X12)
        | X12 = k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X11,esk5_3(X10,X11,X12))
        | ~ r2_lattice3(X10,X11,X12)
        | X12 = k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X12,esk5_3(X10,X11,X12))
        | ~ r2_lattice3(X10,X11,X12)
        | X12 = k1_yellow_0(X10,X11)
        | ~ r1_yellow_0(X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X10))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X9] :
      ( v5_orders_2(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & ( r2_lattice3(esk1_0,esk3_0,esk2_0)
        | esk2_0 = k1_yellow_0(esk1_0,esk3_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,esk2_0,X9)
        | esk2_0 = k1_yellow_0(esk1_0,esk3_0) )
      & ( esk2_0 != k1_yellow_0(esk1_0,esk3_0)
        | ~ r1_yellow_0(esk1_0,esk3_0)
        | esk2_0 = k1_yellow_0(esk1_0,esk3_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk2_0)
        | r1_yellow_0(esk1_0,esk3_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,esk2_0,X9)
        | r1_yellow_0(esk1_0,esk3_0) )
      & ( esk2_0 != k1_yellow_0(esk1_0,esk3_0)
        | ~ r1_yellow_0(esk1_0,esk3_0)
        | r1_yellow_0(esk1_0,esk3_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk2_0)
        | m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,esk2_0,X9)
        | m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( esk2_0 != k1_yellow_0(esk1_0,esk3_0)
        | ~ r1_yellow_0(esk1_0,esk3_0)
        | m1_subset_1(esk4_0,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk2_0)
        | r2_lattice3(esk1_0,esk3_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,esk2_0,X9)
        | r2_lattice3(esk1_0,esk3_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( esk2_0 != k1_yellow_0(esk1_0,esk3_0)
        | ~ r1_yellow_0(esk1_0,esk3_0)
        | r2_lattice3(esk1_0,esk3_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( r2_lattice3(esk1_0,esk3_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ r2_lattice3(esk1_0,esk3_0,X9)
        | r1_orders_2(esk1_0,esk2_0,X9)
        | ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) )
      & ( esk2_0 != k1_yellow_0(esk1_0,esk3_0)
        | ~ r1_yellow_0(esk1_0,esk3_0)
        | ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
        | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])])).

fof(c_0_7,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( m1_subset_1(esk9_2(X22,X23),u1_struct_0(X22))
        | ~ r1_yellow_0(X22,X23)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_lattice3(X22,X23,esk9_2(X22,X23))
        | ~ r1_yellow_0(X22,X23)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_lattice3(X22,X23,X25)
        | r1_orders_2(X22,esk9_2(X22,X23),X25)
        | ~ r1_yellow_0(X22,X23)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk10_3(X22,X26,X27),u1_struct_0(X22))
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r2_lattice3(X22,X26,X27)
        | r1_yellow_0(X22,X26)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_lattice3(X22,X26,esk10_3(X22,X26,X27))
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r2_lattice3(X22,X26,X27)
        | r1_yellow_0(X22,X26)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X27,esk10_3(X22,X26,X27))
        | ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r2_lattice3(X22,X26,X27)
        | r1_yellow_0(X22,X26)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

cnf(c_0_8,plain,
    ( r2_lattice3(X1,X2,esk5_3(X1,X2,X3))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk2_0)
    | esk2_0 = k1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r2_lattice3(X1,X2,esk10_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk10_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk5_3(esk1_0,esk3_0,esk2_0))
    | ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | r1_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_9]),c_0_10]),c_0_11]),c_0_13])])).

cnf(c_0_17,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_yellow_0(esk1_0,esk3_0)
    | m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_9]),c_0_10]),c_0_11]),c_0_13])])).

cnf(c_0_18,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,X1)
    | esk2_0 = k1_yellow_0(esk1_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | r2_lattice3(esk1_0,esk3_0,esk5_3(esk1_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk5_3(esk1_0,esk3_0,esk2_0))
    | m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_17])).

cnf(c_0_21,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk10_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | r2_lattice3(esk1_0,esk3_0,esk5_3(esk1_0,esk3_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk2_0)
    | r1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk5_3(esk1_0,esk3_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_10]),c_0_11]),c_0_13])]),c_0_23]),c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0))
    | ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_27,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk5_3(esk1_0,esk3_0,esk2_0))
    | ~ m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_29,plain,
    ( X2 = k1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk5_3(X1,X3,X2))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ r1_yellow_0(X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_30,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk5_3(esk1_0,esk3_0,esk2_0))
    | r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_10]),c_0_11])]),c_0_16]),c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | ~ m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_33,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0))
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_35,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | m1_subset_1(esk5_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_34]),c_0_10]),c_0_11]),c_0_13])]),c_0_23]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk5_3(esk1_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_35])).

fof(c_0_37,plain,(
    ! [X15,X16] :
      ( ~ l1_orders_2(X15)
      | m1_subset_1(k1_yellow_0(X15,X16),u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_38,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_36]),c_0_10]),c_0_11])]),c_0_9])).

cnf(c_0_39,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_42,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_39]),c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk10_3(esk1_0,esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,k1_yellow_0(esk1_0,esk3_0))
    | r2_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_23]),c_0_11])])).

cnf(c_0_45,negated_conjecture,
    ( k1_yellow_0(esk1_0,esk3_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_43]),c_0_10]),c_0_11]),c_0_13])]),c_0_23]),c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0)
    | ~ r1_yellow_0(esk1_0,esk3_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_47,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,X1)
    | r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk3_0,X1)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_49,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_45])]),c_0_47])])).

cnf(c_0_50,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | r1_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_47]),c_0_10]),c_0_11]),c_0_13])])).

cnf(c_0_51,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk3_0)
    | m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_47]),c_0_10]),c_0_11]),c_0_13])])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,X1)
    | r2_lattice3(esk1_0,esk3_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0)
    | m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_51])).

cnf(c_0_55,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk10_3(esk1_0,esk3_0,esk2_0))
    | r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | esk2_0 != k1_yellow_0(esk1_0,esk3_0)
    | ~ r1_yellow_0(esk1_0,esk3_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 != k1_yellow_0(esk1_0,esk3_0)
    | ~ r1_yellow_0(esk1_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_59,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_55]),c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_56]),c_0_47]),c_0_10]),c_0_11]),c_0_13])]),c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    | ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_45])]),c_0_47])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk4_0)
    | ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_45])]),c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_45]),c_0_11])]),c_0_61]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,X1)
    | r1_yellow_0(esk1_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_65,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk10_3(esk1_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[c_0_50,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk10_3(esk1_0,esk3_0,esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_51,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk10_3(esk1_0,esk3_0,esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_67]),c_0_47]),c_0_10]),c_0_11]),c_0_13])]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
