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
% DateTime   : Thu Dec  3 11:14:54 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 151 expanded)
%              Number of clauses        :   29 (  61 expanded)
%              Number of leaves         :    4 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  361 (2526 expanded)
%              Number of equality atoms :   29 ( 109 expanded)
%              Maximal formula depth    :   23 (   8 average)
%              Maximal clause size      :   74 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(d11_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                    & r1_orders_2(X1,X4,X2)
                    & r1_orders_2(X1,X4,X3)
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( ( r1_orders_2(X1,X5,X2)
                            & r1_orders_2(X1,X5,X3) )
                         => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(c_0_4,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( r1_orders_2(X16,X19,X17)
        | X19 != k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,X19,X18)
        | X19 != k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X16))
        | ~ r1_orders_2(X16,X20,X17)
        | ~ r1_orders_2(X16,X20,X18)
        | r1_orders_2(X16,X20,X19)
        | X19 != k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( m1_subset_1(esk5_4(X16,X17,X18,X19),u1_struct_0(X16))
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,esk5_4(X16,X17,X18,X19),X17)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( r1_orders_2(X16,esk5_4(X16,X17,X18,X19),X18)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) )
      & ( ~ r1_orders_2(X16,esk5_4(X16,X17,X18,X19),X19)
        | ~ r1_orders_2(X16,X19,X17)
        | ~ r1_orders_2(X16,X19,X18)
        | X19 = k11_lattice3(X16,X17,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X16))
        | ~ m1_subset_1(X18,u1_struct_0(X16))
        | ~ m1_subset_1(X17,u1_struct_0(X16))
        | v2_struct_0(X16)
        | ~ v5_orders_2(X16)
        | ~ v2_lattice3(X16)
        | ~ l1_orders_2(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_5,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v2_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_6,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X11,X14] :
      ( ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,esk1_3(X7,X8,X9),X8)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,esk1_3(X7,X8,X9),X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X11,X8)
        | ~ r1_orders_2(X7,X11,X9)
        | r1_orders_2(X7,X11,esk1_3(X7,X8,X9))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk2_1(X7),u1_struct_0(X7))
        | v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk3_1(X7),u1_struct_0(X7))
        | v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk4_2(X7,X14),u1_struct_0(X7))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X14,esk2_1(X7))
        | ~ r1_orders_2(X7,X14,esk3_1(X7))
        | v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,esk4_2(X7,X14),esk2_1(X7))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X14,esk2_1(X7))
        | ~ r1_orders_2(X7,X14,esk3_1(X7))
        | v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r1_orders_2(X7,esk4_2(X7,X14),esk3_1(X7))
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X14,esk2_1(X7))
        | ~ r1_orders_2(X7,X14,esk3_1(X7))
        | v2_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,esk4_2(X7,X14),X14)
        | ~ m1_subset_1(X14,u1_struct_0(X7))
        | ~ r1_orders_2(X7,X14,esk2_1(X7))
        | ~ r1_orders_2(X7,X14,esk3_1(X7))
        | v2_lattice3(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_lattice3])])])])])).

cnf(c_0_9,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,esk5_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r1_orders_2(X2,X1,esk1_3(X2,X3,X4))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X3)
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

cnf(c_0_13,plain,
    ( r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X2)
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

cnf(c_0_14,plain,
    ( esk1_3(X1,X2,X3) = k11_lattice3(X1,X4,X5)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk5_4(X1,X4,X5,esk1_3(X1,X2,X3)),X3)
    | ~ r1_orders_2(X1,esk5_4(X1,X4,X5,esk1_3(X1,X2,X3)),X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X5)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X4)
    | ~ m1_subset_1(esk5_4(X1,X4,X5,esk1_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])).

cnf(c_0_15,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk5_4(X2,X3,X4,X1),X4)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_12,c_0_7])).

cnf(c_0_16,plain,
    ( r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk5_4(X2,X3,X4,X1),X3)
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_7])).

cnf(c_0_18,plain,
    ( esk1_3(X1,X2,X3) = k11_lattice3(X1,X4,X3)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk5_4(X1,X4,X3,esk1_3(X1,X2,X3)),X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X4)
    | ~ m1_subset_1(esk5_4(X1,X4,X3,esk1_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_11]),c_0_16])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,esk1_3(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk5_4(X1,X2,X3,X4),u1_struct_0(X1))
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

cnf(c_0_21,plain,
    ( esk1_3(X1,X2,X3) = k11_lattice3(X1,X3,X4)
    | ~ v5_orders_2(X1)
    | ~ r1_orders_2(X1,esk5_4(X1,X3,X4,esk1_3(X1,X2,X3)),X2)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X4)
    | ~ m1_subset_1(esk5_4(X1,X3,X4,esk1_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_17]),c_0_11]),c_0_16])).

cnf(c_0_22,plain,
    ( esk1_3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(esk5_4(X1,X2,X3,esk1_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_17]),c_0_11]),c_0_16]),c_0_19])).

cnf(c_0_23,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | m1_subset_1(esk5_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_20,c_0_7])).

cnf(c_0_24,plain,
    ( esk1_3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(esk5_4(X1,X3,X2,esk1_3(X1,X2,X3)),u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_11]),c_0_16]),c_0_19])).

fof(c_0_25,negated_conjecture,(
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

cnf(c_0_26,plain,
    ( esk1_3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_11]),c_0_19]),c_0_16])).

cnf(c_0_27,plain,
    ( esk1_3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_11]),c_0_16]),c_0_19])).

fof(c_0_28,negated_conjecture,
    ( v5_orders_2(esk6_0)
    & v2_lattice3(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    & k11_lattice3(esk6_0,esk7_0,esk8_0) != k11_lattice3(esk6_0,esk8_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_29,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( v2_lattice3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k11_lattice3(esk6_0,esk7_0,esk8_0) != k11_lattice3(esk6_0,esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k11_lattice3(esk6_0,X1,X2) = k11_lattice3(esk6_0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:33:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.016 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 0.19/0.40  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.19/0.40  fof(d11_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>?[X4]:(((m1_subset_1(X4,u1_struct_0(X1))&r1_orders_2(X1,X4,X2))&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_lattice3)).
% 0.19/0.40  fof(t15_lattice3, conjecture, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 0.19/0.40  fof(c_0_4, plain, ![X16, X17, X18, X19, X20]:((((r1_orders_2(X16,X19,X17)|X19!=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,X19,X18)|X19!=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16))))&(~m1_subset_1(X20,u1_struct_0(X16))|(~r1_orders_2(X16,X20,X17)|~r1_orders_2(X16,X20,X18)|r1_orders_2(X16,X20,X19))|X19!=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16))))&((m1_subset_1(esk5_4(X16,X17,X18,X19),u1_struct_0(X16))|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))&(((r1_orders_2(X16,esk5_4(X16,X17,X18,X19),X17)|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))&(r1_orders_2(X16,esk5_4(X16,X17,X18,X19),X18)|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16))))&(~r1_orders_2(X16,esk5_4(X16,X17,X18,X19),X19)|(~r1_orders_2(X16,X19,X17)|~r1_orders_2(X16,X19,X18))|X19=k11_lattice3(X16,X17,X18)|~m1_subset_1(X19,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~m1_subset_1(X17,u1_struct_0(X16))|(v2_struct_0(X16)|~v5_orders_2(X16)|~v2_lattice3(X16)|~l1_orders_2(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.19/0.40  fof(c_0_5, plain, ![X6]:(~l1_orders_2(X6)|(~v2_lattice3(X6)|~v2_struct_0(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.19/0.40  cnf(c_0_6, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_7, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.40  fof(c_0_8, plain, ![X7, X8, X9, X11, X14]:(((((m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|~v2_lattice3(X7)|~l1_orders_2(X7))&(r1_orders_2(X7,esk1_3(X7,X8,X9),X8)|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|~v2_lattice3(X7)|~l1_orders_2(X7)))&(r1_orders_2(X7,esk1_3(X7,X8,X9),X9)|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|~v2_lattice3(X7)|~l1_orders_2(X7)))&(~m1_subset_1(X11,u1_struct_0(X7))|(~r1_orders_2(X7,X11,X8)|~r1_orders_2(X7,X11,X9)|r1_orders_2(X7,X11,esk1_3(X7,X8,X9)))|~m1_subset_1(X9,u1_struct_0(X7))|~m1_subset_1(X8,u1_struct_0(X7))|~v2_lattice3(X7)|~l1_orders_2(X7)))&((m1_subset_1(esk2_1(X7),u1_struct_0(X7))|v2_lattice3(X7)|~l1_orders_2(X7))&((m1_subset_1(esk3_1(X7),u1_struct_0(X7))|v2_lattice3(X7)|~l1_orders_2(X7))&((m1_subset_1(esk4_2(X7,X14),u1_struct_0(X7))|(~m1_subset_1(X14,u1_struct_0(X7))|~r1_orders_2(X7,X14,esk2_1(X7))|~r1_orders_2(X7,X14,esk3_1(X7)))|v2_lattice3(X7)|~l1_orders_2(X7))&(((r1_orders_2(X7,esk4_2(X7,X14),esk2_1(X7))|(~m1_subset_1(X14,u1_struct_0(X7))|~r1_orders_2(X7,X14,esk2_1(X7))|~r1_orders_2(X7,X14,esk3_1(X7)))|v2_lattice3(X7)|~l1_orders_2(X7))&(r1_orders_2(X7,esk4_2(X7,X14),esk3_1(X7))|(~m1_subset_1(X14,u1_struct_0(X7))|~r1_orders_2(X7,X14,esk2_1(X7))|~r1_orders_2(X7,X14,esk3_1(X7)))|v2_lattice3(X7)|~l1_orders_2(X7)))&(~r1_orders_2(X7,esk4_2(X7,X14),X14)|(~m1_subset_1(X14,u1_struct_0(X7))|~r1_orders_2(X7,X14,esk2_1(X7))|~r1_orders_2(X7,X14,esk3_1(X7)))|v2_lattice3(X7)|~l1_orders_2(X7))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_lattice3])])])])])).
% 0.19/0.40  cnf(c_0_9, plain, (X1=k11_lattice3(X2,X3,X4)|~v5_orders_2(X2)|~r1_orders_2(X2,esk5_4(X2,X3,X4,X1),X1)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_6, c_0_7])).
% 0.19/0.40  cnf(c_0_10, plain, (r1_orders_2(X2,X1,esk1_3(X2,X3,X4))|~m1_subset_1(X1,u1_struct_0(X2))|~r1_orders_2(X2,X1,X3)|~r1_orders_2(X2,X1,X4)|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_11, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_12, plain, (r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X3)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_13, plain, (r1_orders_2(X1,esk5_4(X1,X2,X3,X4),X2)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_14, plain, (esk1_3(X1,X2,X3)=k11_lattice3(X1,X4,X5)|~v5_orders_2(X1)|~r1_orders_2(X1,esk5_4(X1,X4,X5,esk1_3(X1,X2,X3)),X3)|~r1_orders_2(X1,esk5_4(X1,X4,X5,esk1_3(X1,X2,X3)),X2)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X5)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X4)|~m1_subset_1(esk5_4(X1,X4,X5,esk1_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])).
% 0.19/0.40  cnf(c_0_15, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk5_4(X2,X3,X4,X1),X4)|~v5_orders_2(X2)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_12, c_0_7])).
% 0.19/0.40  cnf(c_0_16, plain, (r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_17, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk5_4(X2,X3,X4,X1),X3)|~v5_orders_2(X2)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_13, c_0_7])).
% 0.19/0.40  cnf(c_0_18, plain, (esk1_3(X1,X2,X3)=k11_lattice3(X1,X4,X3)|~v5_orders_2(X1)|~r1_orders_2(X1,esk5_4(X1,X4,X3,esk1_3(X1,X2,X3)),X2)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X4)|~m1_subset_1(esk5_4(X1,X4,X3,esk1_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_11]), c_0_16])).
% 0.19/0.40  cnf(c_0_19, plain, (r1_orders_2(X1,esk1_3(X1,X2,X3),X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_20, plain, (m1_subset_1(esk5_4(X1,X2,X3,X4),u1_struct_0(X1))|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.19/0.40  cnf(c_0_21, plain, (esk1_3(X1,X2,X3)=k11_lattice3(X1,X3,X4)|~v5_orders_2(X1)|~r1_orders_2(X1,esk5_4(X1,X3,X4,esk1_3(X1,X2,X3)),X2)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X4)|~m1_subset_1(esk5_4(X1,X3,X4,esk1_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_17]), c_0_11]), c_0_16])).
% 0.19/0.40  cnf(c_0_22, plain, (esk1_3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~m1_subset_1(esk5_4(X1,X2,X3,esk1_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_17]), c_0_11]), c_0_16]), c_0_19])).
% 0.19/0.40  cnf(c_0_23, plain, (X1=k11_lattice3(X2,X3,X4)|m1_subset_1(esk5_4(X2,X3,X4,X1),u1_struct_0(X2))|~v5_orders_2(X2)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[c_0_20, c_0_7])).
% 0.19/0.40  cnf(c_0_24, plain, (esk1_3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~m1_subset_1(esk5_4(X1,X3,X2,esk1_3(X1,X2,X3)),u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_15]), c_0_11]), c_0_16]), c_0_19])).
% 0.19/0.40  fof(c_0_25, negated_conjecture, ~(![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2))))), inference(assume_negation,[status(cth)],[t15_lattice3])).
% 0.19/0.40  cnf(c_0_26, plain, (esk1_3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_11]), c_0_19]), c_0_16])).
% 0.19/0.40  cnf(c_0_27, plain, (esk1_3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_11]), c_0_16]), c_0_19])).
% 0.19/0.40  fof(c_0_28, negated_conjecture, (((v5_orders_2(esk6_0)&v2_lattice3(esk6_0))&l1_orders_2(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(m1_subset_1(esk8_0,u1_struct_0(esk6_0))&k11_lattice3(esk6_0,esk7_0,esk8_0)!=k11_lattice3(esk6_0,esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.19/0.40  cnf(c_0_29, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.40  cnf(c_0_30, negated_conjecture, (v5_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (v2_lattice3(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (k11_lattice3(esk6_0,esk7_0,esk8_0)!=k11_lattice3(esk6_0,esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (k11_lattice3(esk6_0,X1,X2)=k11_lattice3(esk6_0,X2,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 38
% 0.19/0.40  # Proof object clause steps            : 29
% 0.19/0.40  # Proof object formula steps           : 9
% 0.19/0.40  # Proof object conjectures             : 11
% 0.19/0.40  # Proof object clause conjectures      : 8
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 15
% 0.19/0.40  # Proof object initial formulas used   : 4
% 0.19/0.40  # Proof object generating inferences   : 10
% 0.19/0.40  # Proof object simplifying inferences  : 27
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 4
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 24
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 24
% 0.19/0.40  # Processed clauses                    : 458
% 0.19/0.40  # ...of these trivial                  : 13
% 0.19/0.40  # ...subsumed                          : 264
% 0.19/0.40  # ...remaining for further processing  : 181
% 0.19/0.40  # Other redundant clauses eliminated   : 53
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 45
% 0.19/0.40  # Backward-rewritten                   : 0
% 0.19/0.40  # Generated clauses                    : 1534
% 0.19/0.40  # ...of the previous two non-trivial   : 1163
% 0.19/0.40  # Contextual simplify-reflections      : 54
% 0.19/0.40  # Paramodulations                      : 1474
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 60
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 112
% 0.19/0.40  #    Positive orientable unit clauses  : 5
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 1
% 0.19/0.40  #    Non-unit-clauses                  : 106
% 0.19/0.40  # Current number of unprocessed clauses: 707
% 0.19/0.40  # ...number of literals in the above   : 7811
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 69
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 10937
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 865
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 363
% 0.19/0.40  # Unit Clause-clause subsumption calls : 0
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 0
% 0.19/0.40  # BW rewrite match successes           : 0
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 76710
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.059 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.065 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
