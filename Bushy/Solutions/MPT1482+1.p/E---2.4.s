%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : lattice3__t15_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 8.45s
% Output     : CNFRefutation 8.45s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 488 expanded)
%              Number of clauses        :   38 ( 167 expanded)
%              Number of leaves         :    4 ( 120 expanded)
%              Depth                    :    9
%              Number of atoms          :  301 (3241 expanded)
%              Number of equality atoms :   27 ( 372 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   74 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',cc2_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',dt_k11_lattice3)).

fof(t15_lattice3,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t15_lattice3.p',t15_lattice3)).

fof(c_0_4,plain,(
    ! [X27,X28,X29,X30,X31] :
      ( ( r1_orders_2(X27,X30,X28)
        | X30 != k11_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) )
      & ( r1_orders_2(X27,X30,X29)
        | X30 != k11_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X27))
        | ~ r1_orders_2(X27,X31,X28)
        | ~ r1_orders_2(X27,X31,X29)
        | r1_orders_2(X27,X31,X30)
        | X30 != k11_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk9_4(X27,X28,X29,X30),u1_struct_0(X27))
        | ~ r1_orders_2(X27,X30,X28)
        | ~ r1_orders_2(X27,X30,X29)
        | X30 = k11_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) )
      & ( r1_orders_2(X27,esk9_4(X27,X28,X29,X30),X28)
        | ~ r1_orders_2(X27,X30,X28)
        | ~ r1_orders_2(X27,X30,X29)
        | X30 = k11_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) )
      & ( r1_orders_2(X27,esk9_4(X27,X28,X29,X30),X29)
        | ~ r1_orders_2(X27,X30,X28)
        | ~ r1_orders_2(X27,X30,X29)
        | X30 = k11_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) )
      & ( ~ r1_orders_2(X27,esk9_4(X27,X28,X29,X30),X30)
        | ~ r1_orders_2(X27,X30,X28)
        | ~ r1_orders_2(X27,X30,X29)
        | X30 = k11_lattice3(X27,X28,X29)
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v5_orders_2(X27)
        | ~ v2_lattice3(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_5,plain,(
    ! [X42] :
      ( ~ l1_orders_2(X42)
      | ~ v2_lattice3(X42)
      | ~ v2_struct_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_6,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | m1_subset_1(k11_lattice3(X19,X20,X21),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t15_lattice3])).

cnf(c_0_8,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X3,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( v5_orders_2(esk1_0)
    & v2_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & k11_lattice3(esk1_0,esk2_0,esk3_0) != k11_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_8,c_0_9])]),c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X2 != k11_lattice3(X1,X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,plain,
    ( r1_orders_2(X1,esk9_4(X1,X2,X3,X4),X2)
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( r1_orders_2(esk1_0,k11_lattice3(esk1_0,X1,esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(k11_lattice3(esk1_0,X1,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_13]),c_0_14])])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,k11_lattice3(X1,X2,X3),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_17,c_0_9])]),c_0_10])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk9_4(X1,X2,X3,X4),u1_struct_0(X1))
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk9_4(X2,X3,X4,X1),X3)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_18,c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k11_lattice3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk2_0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_28,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | m1_subset_1(esk9_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_23,c_0_9])).

cnf(c_0_29,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk9_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,esk9_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_31,plain,
    ( r1_orders_2(X2,X1,X5)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X1,X4)
    | X5 != k11_lattice3(X2,X3,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_32,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk3_0) = k11_lattice3(esk1_0,X1,esk2_0)
    | r1_orders_2(esk1_0,esk9_4(esk1_0,X1,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),X1)
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_20]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk2_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk3_0) != k11_lattice3(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk3_0) = k11_lattice3(esk1_0,X1,esk2_0)
    | m1_subset_1(esk9_4(esk1_0,X1,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26]),c_0_20]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_36,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,esk9_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_9])).

cnf(c_0_37,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk9_4(X2,X3,X4,X1),X4)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ v5_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_9])).

cnf(c_0_38,plain,
    ( r1_orders_2(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_9])]),c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk1_0,esk9_4(esk1_0,esk3_0,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_13])]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk9_4(esk1_0,esk3_0,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_13])]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk3_0) = k11_lattice3(esk1_0,X1,esk2_0)
    | ~ r1_orders_2(esk1_0,esk9_4(esk1_0,X1,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),k11_lattice3(esk1_0,esk2_0,esk3_0))
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_26]),c_0_20]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_42,negated_conjecture,
    ( k11_lattice3(esk1_0,esk2_0,esk3_0) = k11_lattice3(esk1_0,X1,esk2_0)
    | r1_orders_2(esk1_0,esk9_4(esk1_0,X1,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),esk2_0)
    | ~ r1_orders_2(esk1_0,k11_lattice3(esk1_0,esk2_0,esk3_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_26]),c_0_20]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk1_0,esk9_4(esk1_0,esk3_0,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),k11_lattice3(esk1_0,X1,esk3_0))
    | ~ r1_orders_2(esk1_0,esk9_4(esk1_0,esk3_0,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_13]),c_0_40]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk9_4(esk1_0,esk3_0,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),k11_lattice3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_33]),c_0_13])]),c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk1_0,esk9_4(esk1_0,esk3_0,esk2_0,k11_lattice3(esk1_0,esk2_0,esk3_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_13])]),c_0_34])).

cnf(c_0_46,plain,
    ( $false ),
    inference(cdclpropres,[status(thm)],[c_0_43,c_0_44,c_0_45,c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
