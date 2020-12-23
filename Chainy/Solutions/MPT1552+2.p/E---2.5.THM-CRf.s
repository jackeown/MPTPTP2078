%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1552+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:06 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :   52 (1836 expanded)
%              Number of clauses        :   41 ( 665 expanded)
%              Number of leaves         :    5 ( 441 expanded)
%              Depth                    :   13
%              Number of atoms          :  294 (30355 expanded)
%              Number of equality atoms :   36 (3908 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   57 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(t25_orders_2,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_orders_2(X1,X2,X3)
                  & r1_orders_2(X1,X3,X2) )
               => X2 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT017+2.ax',t25_orders_2)).

fof(c_0_5,plain,(
    ! [X9487,X9488,X9489,X9490] :
      ( ( r2_lattice3(X9487,X9488,X9489)
        | X9489 != k1_yellow_0(X9487,X9488)
        | ~ r1_yellow_0(X9487,X9488)
        | ~ m1_subset_1(X9489,u1_struct_0(X9487))
        | ~ l1_orders_2(X9487) )
      & ( ~ m1_subset_1(X9490,u1_struct_0(X9487))
        | ~ r2_lattice3(X9487,X9488,X9490)
        | r1_orders_2(X9487,X9489,X9490)
        | X9489 != k1_yellow_0(X9487,X9488)
        | ~ r1_yellow_0(X9487,X9488)
        | ~ m1_subset_1(X9489,u1_struct_0(X9487))
        | ~ l1_orders_2(X9487) )
      & ( m1_subset_1(esk1079_3(X9487,X9488,X9489),u1_struct_0(X9487))
        | ~ r2_lattice3(X9487,X9488,X9489)
        | X9489 = k1_yellow_0(X9487,X9488)
        | ~ r1_yellow_0(X9487,X9488)
        | ~ m1_subset_1(X9489,u1_struct_0(X9487))
        | ~ l1_orders_2(X9487) )
      & ( r2_lattice3(X9487,X9488,esk1079_3(X9487,X9488,X9489))
        | ~ r2_lattice3(X9487,X9488,X9489)
        | X9489 = k1_yellow_0(X9487,X9488)
        | ~ r1_yellow_0(X9487,X9488)
        | ~ m1_subset_1(X9489,u1_struct_0(X9487))
        | ~ l1_orders_2(X9487) )
      & ( ~ r1_orders_2(X9487,X9489,esk1079_3(X9487,X9488,X9489))
        | ~ r2_lattice3(X9487,X9488,X9489)
        | X9489 = k1_yellow_0(X9487,X9488)
        | ~ r1_yellow_0(X9487,X9488)
        | ~ m1_subset_1(X9489,u1_struct_0(X9487))
        | ~ l1_orders_2(X9487) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_6,plain,(
    ! [X9493,X9494] :
      ( ~ l1_orders_2(X9493)
      | m1_subset_1(k1_yellow_0(X9493,X9494),u1_struct_0(X9493)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

fof(c_0_7,negated_conjecture,(
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

cnf(c_0_8,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,(
    ! [X9600] :
      ( v5_orders_2(esk1095_0)
      & l1_orders_2(esk1095_0)
      & m1_subset_1(esk1096_0,u1_struct_0(esk1095_0))
      & ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0)
        | esk1096_0 = k1_yellow_0(esk1095_0,esk1097_0) )
      & ( ~ m1_subset_1(X9600,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,X9600)
        | r1_orders_2(esk1095_0,esk1096_0,X9600)
        | esk1096_0 = k1_yellow_0(esk1095_0,esk1097_0) )
      & ( esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
        | ~ r1_yellow_0(esk1095_0,esk1097_0)
        | esk1096_0 = k1_yellow_0(esk1095_0,esk1097_0) )
      & ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0)
        | r1_yellow_0(esk1095_0,esk1097_0) )
      & ( ~ m1_subset_1(X9600,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,X9600)
        | r1_orders_2(esk1095_0,esk1096_0,X9600)
        | r1_yellow_0(esk1095_0,esk1097_0) )
      & ( esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
        | ~ r1_yellow_0(esk1095_0,esk1097_0)
        | r1_yellow_0(esk1095_0,esk1097_0) )
      & ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0)
        | m1_subset_1(esk1098_0,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( ~ m1_subset_1(X9600,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,X9600)
        | r1_orders_2(esk1095_0,esk1096_0,X9600)
        | m1_subset_1(esk1098_0,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
        | ~ r1_yellow_0(esk1095_0,esk1097_0)
        | m1_subset_1(esk1098_0,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0)
        | r2_lattice3(esk1095_0,esk1097_0,esk1098_0)
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( ~ m1_subset_1(X9600,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,X9600)
        | r1_orders_2(esk1095_0,esk1096_0,X9600)
        | r2_lattice3(esk1095_0,esk1097_0,esk1098_0)
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
        | ~ r1_yellow_0(esk1095_0,esk1097_0)
        | r2_lattice3(esk1095_0,esk1097_0,esk1098_0)
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0)
        | ~ r1_orders_2(esk1095_0,esk1096_0,esk1098_0)
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( ~ m1_subset_1(X9600,u1_struct_0(esk1095_0))
        | ~ r2_lattice3(esk1095_0,esk1097_0,X9600)
        | r1_orders_2(esk1095_0,esk1096_0,X9600)
        | ~ r1_orders_2(esk1095_0,esk1096_0,esk1098_0)
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) )
      & ( esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
        | ~ r1_yellow_0(esk1095_0,esk1097_0)
        | ~ r1_orders_2(esk1095_0,esk1096_0,esk1098_0)
        | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])).

cnf(c_0_11,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_8]),c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0)
    | r1_yellow_0(esk1095_0,esk1097_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk1095_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X9525,X9526,X9528,X9529,X9530] :
      ( ( m1_subset_1(esk1085_2(X9525,X9526),u1_struct_0(X9525))
        | ~ r1_yellow_0(X9525,X9526)
        | ~ v5_orders_2(X9525)
        | ~ l1_orders_2(X9525) )
      & ( r2_lattice3(X9525,X9526,esk1085_2(X9525,X9526))
        | ~ r1_yellow_0(X9525,X9526)
        | ~ v5_orders_2(X9525)
        | ~ l1_orders_2(X9525) )
      & ( ~ m1_subset_1(X9528,u1_struct_0(X9525))
        | ~ r2_lattice3(X9525,X9526,X9528)
        | r1_orders_2(X9525,esk1085_2(X9525,X9526),X9528)
        | ~ r1_yellow_0(X9525,X9526)
        | ~ v5_orders_2(X9525)
        | ~ l1_orders_2(X9525) )
      & ( m1_subset_1(esk1086_3(X9525,X9529,X9530),u1_struct_0(X9525))
        | ~ m1_subset_1(X9530,u1_struct_0(X9525))
        | ~ r2_lattice3(X9525,X9529,X9530)
        | r1_yellow_0(X9525,X9529)
        | ~ v5_orders_2(X9525)
        | ~ l1_orders_2(X9525) )
      & ( r2_lattice3(X9525,X9529,esk1086_3(X9525,X9529,X9530))
        | ~ m1_subset_1(X9530,u1_struct_0(X9525))
        | ~ r2_lattice3(X9525,X9529,X9530)
        | r1_yellow_0(X9525,X9529)
        | ~ v5_orders_2(X9525)
        | ~ l1_orders_2(X9525) )
      & ( ~ r1_orders_2(X9525,X9530,esk1086_3(X9525,X9529,X9530))
        | ~ m1_subset_1(X9530,u1_struct_0(X9525))
        | ~ r2_lattice3(X9525,X9529,X9530)
        | r1_yellow_0(X9525,X9529)
        | ~ v5_orders_2(X9525)
        | ~ l1_orders_2(X9525) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,k1_yellow_0(esk1095_0,esk1097_0))
    | r2_lattice3(esk1095_0,esk1097_0,esk1096_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_16,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0)
    | esk1096_0 = k1_yellow_0(esk1095_0,esk1097_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_lattice3(X1,X2,esk1086_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,esk1096_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v5_orders_2(esk1095_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk1096_0,u1_struct_0(esk1095_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1086_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,negated_conjecture,
    ( r1_orders_2(esk1095_0,esk1096_0,X1)
    | r1_yellow_0(esk1095_0,esk1097_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1095_0))
    | ~ r2_lattice3(esk1095_0,esk1097_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( r1_yellow_0(esk1095_0,esk1097_0)
    | r2_lattice3(esk1095_0,esk1097_0,esk1086_3(esk1095_0,esk1097_0,esk1096_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_13]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( r1_yellow_0(esk1095_0,esk1097_0)
    | m1_subset_1(esk1086_3(esk1095_0,esk1097_0,esk1096_0),u1_struct_0(esk1095_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19]),c_0_13]),c_0_20])])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_9])).

cnf(c_0_27,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk1086_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( r1_yellow_0(esk1095_0,esk1097_0)
    | r1_orders_2(esk1095_0,esk1096_0,esk1086_3(esk1095_0,esk1097_0,esk1096_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_29,plain,(
    ! [X6353,X6354,X6355] :
      ( ~ v5_orders_2(X6353)
      | ~ l1_orders_2(X6353)
      | ~ m1_subset_1(X6354,u1_struct_0(X6353))
      | ~ m1_subset_1(X6355,u1_struct_0(X6353))
      | ~ r1_orders_2(X6353,X6354,X6355)
      | ~ r1_orders_2(X6353,X6355,X6354)
      | X6354 = X6355 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_orders_2])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk1095_0,k1_yellow_0(esk1095_0,esk1097_0),esk1096_0)
    | ~ r1_yellow_0(esk1095_0,esk1097_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_13]),c_0_20])])).

cnf(c_0_31,negated_conjecture,
    ( r1_yellow_0(esk1095_0,esk1097_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_18]),c_0_19]),c_0_13]),c_0_20])])).

cnf(c_0_32,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,esk1098_0)
    | esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
    | ~ r1_yellow_0(esk1095_0,esk1097_0)
    | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( X2 = X3
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk1095_0,k1_yellow_0(esk1095_0,esk1097_0),esk1096_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k1_yellow_0(esk1095_0,X1),u1_struct_0(esk1095_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
    | ~ r1_yellow_0(esk1095_0,esk1097_0)
    | ~ r1_orders_2(esk1095_0,esk1096_0,esk1098_0)
    | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1098_0,u1_struct_0(esk1095_0))
    | esk1096_0 != k1_yellow_0(esk1095_0,esk1097_0)
    | ~ r1_yellow_0(esk1095_0,esk1097_0)
    | ~ r2_lattice3(esk1095_0,esk1097_0,esk1096_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,esk1098_0)
    | k1_yellow_0(esk1095_0,esk1097_0) != esk1096_0
    | ~ r1_yellow_0(esk1095_0,esk1097_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_18])])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk1095_0,esk1096_0,X1)
    | esk1096_0 = k1_yellow_0(esk1095_0,esk1097_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1095_0))
    | ~ r2_lattice3(esk1095_0,esk1097_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,k1_yellow_0(esk1095_0,esk1097_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_31]),c_0_13])])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(esk1095_0,esk1097_0) = esk1096_0
    | ~ r1_orders_2(esk1095_0,esk1096_0,k1_yellow_0(esk1095_0,esk1097_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19]),c_0_13]),c_0_35]),c_0_20])])).

cnf(c_0_42,negated_conjecture,
    ( k1_yellow_0(esk1095_0,esk1097_0) != esk1096_0
    | ~ r1_yellow_0(esk1095_0,esk1097_0)
    | ~ r1_orders_2(esk1095_0,esk1096_0,esk1098_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_18])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1098_0,u1_struct_0(esk1095_0))
    | k1_yellow_0(esk1095_0,esk1097_0) != esk1096_0
    | ~ r1_yellow_0(esk1095_0,esk1097_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_18])])).

cnf(c_0_44,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,esk1098_0)
    | k1_yellow_0(esk1095_0,esk1097_0) != esk1096_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_31])])).

cnf(c_0_45,negated_conjecture,
    ( k1_yellow_0(esk1095_0,esk1097_0) = esk1096_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35])]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k1_yellow_0(esk1095_0,esk1097_0) != esk1096_0
    | ~ r1_orders_2(esk1095_0,esk1096_0,esk1098_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_31])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk1098_0,u1_struct_0(esk1095_0))
    | k1_yellow_0(esk1095_0,esk1097_0) != esk1096_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_31])])).

cnf(c_0_48,negated_conjecture,
    ( r2_lattice3(esk1095_0,esk1097_0,esk1098_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_orders_2(esk1095_0,esk1096_0,esk1098_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_45])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk1098_0,u1_struct_0(esk1095_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_48]),c_0_45]),c_0_31]),c_0_13])]),c_0_49]),c_0_50])]),
    [proof]).
%------------------------------------------------------------------------------
