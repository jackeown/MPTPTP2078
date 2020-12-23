%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_9__t12_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 22.72s
% Output     : CNFRefutation 22.72s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 133 expanded)
%              Number of clauses        :   40 (  56 expanded)
%              Number of leaves         :    6 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  484 (1508 expanded)
%              Number of equality atoms :   51 ( 179 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal clause size      :  110 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d7_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X1)
                    & l1_waybel_0(X4,X1) )
                 => ( X4 = k4_waybel_9(X1,X2,X3)
                  <=> ( ! [X5] :
                          ( r2_hidden(X5,u1_struct_0(X4))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                              & X6 = X5
                              & r1_orders_2(X2,X3,X6) ) )
                      & r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4)))
                      & u1_waybel_0(X1,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t12_waybel_9.p',d7_waybel_9)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t12_waybel_9.p',dt_k4_waybel_9)).

fof(fraenkel_a_3_0_waybel_9,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & ~ v2_struct_0(X3)
        & l1_waybel_0(X3,X2)
        & m1_subset_1(X4,u1_struct_0(X3)) )
     => ( r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
      <=> ? [X5] :
            ( m1_subset_1(X5,u1_struct_0(X3))
            & X1 = X5
            & r1_orders_2(X3,X4,X5) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t12_waybel_9.p',fraenkel_a_3_0_waybel_9)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t12_waybel_9.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t12_waybel_9.p',d10_xboole_0)).

fof(t12_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t12_waybel_9.p',t12_waybel_9)).

fof(c_0_6,plain,(
    ! [X26,X27,X28,X29,X30,X32,X33,X35] :
      ( ( m1_subset_1(esk5_5(X26,X27,X28,X29,X30),u1_struct_0(X27))
        | ~ r2_hidden(X30,u1_struct_0(X29))
        | X29 != k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( esk5_5(X26,X27,X28,X29,X30) = X30
        | ~ r2_hidden(X30,u1_struct_0(X29))
        | X29 != k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( r1_orders_2(X27,X28,esk5_5(X26,X27,X28,X29,X30))
        | ~ r2_hidden(X30,u1_struct_0(X29))
        | X29 != k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( ~ m1_subset_1(X33,u1_struct_0(X27))
        | X33 != X32
        | ~ r1_orders_2(X27,X28,X33)
        | r2_hidden(X32,u1_struct_0(X29))
        | X29 != k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( r2_relset_1(u1_struct_0(X29),u1_struct_0(X29),u1_orders_2(X29),k1_toler_1(u1_orders_2(X27),u1_struct_0(X29)))
        | X29 != k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( u1_waybel_0(X26,X29) = k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),u1_waybel_0(X26,X27),u1_struct_0(X29))
        | X29 != k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( ~ r2_hidden(esk6_4(X26,X27,X28,X29),u1_struct_0(X29))
        | ~ m1_subset_1(X35,u1_struct_0(X27))
        | X35 != esk6_4(X26,X27,X28,X29)
        | ~ r1_orders_2(X27,X28,X35)
        | ~ r2_relset_1(u1_struct_0(X29),u1_struct_0(X29),u1_orders_2(X29),k1_toler_1(u1_orders_2(X27),u1_struct_0(X29)))
        | u1_waybel_0(X26,X29) != k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),u1_waybel_0(X26,X27),u1_struct_0(X29))
        | X29 = k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( m1_subset_1(esk7_4(X26,X27,X28,X29),u1_struct_0(X27))
        | r2_hidden(esk6_4(X26,X27,X28,X29),u1_struct_0(X29))
        | ~ r2_relset_1(u1_struct_0(X29),u1_struct_0(X29),u1_orders_2(X29),k1_toler_1(u1_orders_2(X27),u1_struct_0(X29)))
        | u1_waybel_0(X26,X29) != k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),u1_waybel_0(X26,X27),u1_struct_0(X29))
        | X29 = k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( esk7_4(X26,X27,X28,X29) = esk6_4(X26,X27,X28,X29)
        | r2_hidden(esk6_4(X26,X27,X28,X29),u1_struct_0(X29))
        | ~ r2_relset_1(u1_struct_0(X29),u1_struct_0(X29),u1_orders_2(X29),k1_toler_1(u1_orders_2(X27),u1_struct_0(X29)))
        | u1_waybel_0(X26,X29) != k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),u1_waybel_0(X26,X27),u1_struct_0(X29))
        | X29 = k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) )
      & ( r1_orders_2(X27,X28,esk7_4(X26,X27,X28,X29))
        | r2_hidden(esk6_4(X26,X27,X28,X29),u1_struct_0(X29))
        | ~ r2_relset_1(u1_struct_0(X29),u1_struct_0(X29),u1_orders_2(X29),k1_toler_1(u1_orders_2(X27),u1_struct_0(X29)))
        | u1_waybel_0(X26,X29) != k2_partfun1(u1_struct_0(X27),u1_struct_0(X26),u1_waybel_0(X26,X27),u1_struct_0(X29))
        | X29 = k4_waybel_9(X26,X27,X28)
        | ~ v6_waybel_0(X29,X26)
        | ~ l1_waybel_0(X29,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ l1_waybel_0(X27,X26)
        | v2_struct_0(X26)
        | ~ l1_struct_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,u1_struct_0(X5))
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X1 != X3
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k4_waybel_9(X6,X2,X4)
    | ~ v6_waybel_0(X5,X6)
    | ~ l1_waybel_0(X5,X6)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X6)
    | ~ l1_struct_0(X6) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_8,plain,(
    ! [X49,X50,X51] :
      ( ( v6_waybel_0(k4_waybel_9(X49,X50,X51),X49)
        | v2_struct_0(X49)
        | ~ l1_struct_0(X49)
        | v2_struct_0(X50)
        | ~ l1_waybel_0(X50,X49)
        | ~ m1_subset_1(X51,u1_struct_0(X50)) )
      & ( l1_waybel_0(k4_waybel_9(X49,X50,X51),X49)
        | v2_struct_0(X49)
        | ~ l1_struct_0(X49)
        | v2_struct_0(X50)
        | ~ l1_waybel_0(X50,X49)
        | ~ m1_subset_1(X51,u1_struct_0(X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

fof(c_0_9,plain,(
    ! [X66,X67,X68,X69,X71] :
      ( ( m1_subset_1(esk12_4(X66,X67,X68,X69),u1_struct_0(X68))
        | ~ r2_hidden(X66,a_3_0_waybel_9(X67,X68,X69))
        | v2_struct_0(X67)
        | ~ l1_struct_0(X67)
        | v2_struct_0(X68)
        | ~ l1_waybel_0(X68,X67)
        | ~ m1_subset_1(X69,u1_struct_0(X68)) )
      & ( X66 = esk12_4(X66,X67,X68,X69)
        | ~ r2_hidden(X66,a_3_0_waybel_9(X67,X68,X69))
        | v2_struct_0(X67)
        | ~ l1_struct_0(X67)
        | v2_struct_0(X68)
        | ~ l1_waybel_0(X68,X67)
        | ~ m1_subset_1(X69,u1_struct_0(X68)) )
      & ( r1_orders_2(X68,X69,esk12_4(X66,X67,X68,X69))
        | ~ r2_hidden(X66,a_3_0_waybel_9(X67,X68,X69))
        | v2_struct_0(X67)
        | ~ l1_struct_0(X67)
        | v2_struct_0(X68)
        | ~ l1_waybel_0(X68,X67)
        | ~ m1_subset_1(X69,u1_struct_0(X68)) )
      & ( ~ m1_subset_1(X71,u1_struct_0(X68))
        | X66 != X71
        | ~ r1_orders_2(X68,X69,X71)
        | r2_hidden(X66,a_3_0_waybel_9(X67,X68,X69))
        | v2_struct_0(X67)
        | ~ l1_struct_0(X67)
        | v2_struct_0(X68)
        | ~ l1_waybel_0(X68,X67)
        | ~ m1_subset_1(X69,u1_struct_0(X68)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_3_0_waybel_9])])])])])])).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r1_tarski(X20,X21)
        | ~ r2_hidden(X22,X20)
        | r2_hidden(X22,X21) )
      & ( r2_hidden(esk4_2(X23,X24),X23)
        | r1_tarski(X23,X24) )
      & ( ~ r2_hidden(esk4_2(X23,X24),X24)
        | r1_tarski(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,u1_struct_0(X2))
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | X2 != k4_waybel_9(X3,X4,X5)
    | ~ r1_orders_2(X4,X5,X1)
    | ~ v6_waybel_0(X2,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_waybel_0(X4,X3)
    | ~ l1_struct_0(X3) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = esk12_4(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk12_4(X1,X2,X3,X4),u1_struct_0(X3))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | ~ l1_struct_0(X2)
    | ~ l1_waybel_0(X3,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_orders_2(X1,X2,esk5_5(X3,X1,X2,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X3,X1,X2)
    | ~ v6_waybel_0(X4,X3)
    | ~ l1_waybel_0(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( esk5_5(X1,X2,X3,X4,X5) = X5
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk5_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk4_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,u1_struct_0(k4_waybel_9(X2,X3,X4)))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12]),c_0_13])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,esk12_4(X3,X4,X1,X2))
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_3_0_waybel_9(X4,X1,X2))
    | ~ l1_struct_0(X4)
    | ~ l1_waybel_0(X1,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( esk12_4(esk4_2(a_3_0_waybel_9(X1,X2,X3),X4),X1,X2,X3) = esk4_2(a_3_0_waybel_9(X1,X2,X3),X4)
    | r1_tarski(a_3_0_waybel_9(X1,X2,X3),X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(a_3_0_waybel_9(X1,X2,X3),X4)
    | m1_subset_1(esk12_4(esk4_2(a_3_0_waybel_9(X1,X2,X3),X4),X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,a_3_0_waybel_9(X5,X2,X4))
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ r1_orders_2(X2,X4,X1)
    | ~ l1_struct_0(X5)
    | ~ l1_waybel_0(X2,X5)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | X5 != k4_waybel_9(X4,X1,X2)
    | ~ r2_hidden(X3,u1_struct_0(X5))
    | ~ v6_waybel_0(X5,X4)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X5,X4)
    | ~ l1_waybel_0(X1,X4)
    | ~ l1_struct_0(X4) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | X4 != k4_waybel_9(X3,X2,X5)
    | ~ r2_hidden(X1,u1_struct_0(X4))
    | ~ v6_waybel_0(X4,X3)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ l1_waybel_0(X4,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_28,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,u1_struct_0(k4_waybel_9(X2,X3,X4)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_orders_2(X3,X4,esk4_2(X1,u1_struct_0(k4_waybel_9(X2,X3,X4))))
    | ~ m1_subset_1(esk4_2(X1,u1_struct_0(k4_waybel_9(X2,X3,X4))),u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,esk4_2(a_3_0_waybel_9(X3,X1,X2),X4))
    | r1_tarski(a_3_0_waybel_9(X3,X1,X2),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_15])).

cnf(c_0_31,plain,
    ( r1_tarski(a_3_0_waybel_9(X1,X2,X3),X4)
    | m1_subset_1(esk4_2(a_3_0_waybel_9(X1,X2,X3),X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,a_3_0_waybel_9(X2,X3,X4))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r1_orders_2(X1,X2,esk4_2(u1_struct_0(X3),X4))
    | r1_tarski(u1_struct_0(X3),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | X3 != k4_waybel_9(X5,X1,X2)
    | ~ v6_waybel_0(X3,X5)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X3,X5)
    | ~ l1_waybel_0(X1,X5)
    | ~ l1_struct_0(X5) ),
    inference(spm,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_34,plain,
    ( r1_tarski(u1_struct_0(X1),X2)
    | m1_subset_1(esk4_2(u1_struct_0(X1),X2),u1_struct_0(X3))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | X1 != k4_waybel_9(X4,X3,X5)
    | ~ v6_waybel_0(X1,X4)
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ l1_waybel_0(X1,X4)
    | ~ l1_waybel_0(X3,X4)
    | ~ l1_struct_0(X4) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X1,X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_waybel_9])).

cnf(c_0_36,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(a_3_0_waybel_9(X1,X2,X3),u1_struct_0(k4_waybel_9(X4,X2,X3)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X4)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,a_3_0_waybel_9(X2,X3,X4))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_orders_2(X3,X4,esk4_2(X1,a_3_0_waybel_9(X2,X3,X4)))
    | ~ m1_subset_1(esk4_2(X1,a_3_0_waybel_9(X2,X3,X4)),u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_32])).

cnf(c_0_39,plain,
    ( r1_orders_2(X1,X2,esk4_2(u1_struct_0(k4_waybel_9(X3,X1,X2)),X4))
    | r1_tarski(u1_struct_0(k4_waybel_9(X3,X1,X2)),X4)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_12]),c_0_13])).

cnf(c_0_40,plain,
    ( r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),X4)
    | m1_subset_1(esk4_2(u1_struct_0(k4_waybel_9(X1,X2,X3)),X4),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_12]),c_0_13])).

fof(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & u1_struct_0(k4_waybel_9(esk1_0,esk2_0,esk3_0)) != a_3_0_waybel_9(esk1_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_35])])])])).

cnf(c_0_42,plain,
    ( u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X4,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),a_3_0_waybel_9(X4,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X2,X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X4) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(u1_struct_0(k4_waybel_9(X1,X2,X3)),a_3_0_waybel_9(X4,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X4)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( u1_struct_0(k4_waybel_9(esk1_0,esk2_0,esk3_0)) != a_3_0_waybel_9(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( u1_struct_0(k4_waybel_9(X1,X2,X3)) = a_3_0_waybel_9(X4,X2,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X2,X4)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X4) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v2_struct_0(X1)
    | u1_struct_0(k4_waybel_9(X1,esk2_0,esk3_0)) != u1_struct_0(k4_waybel_9(esk1_0,esk2_0,esk3_0))
    | ~ l1_waybel_0(esk2_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])]),c_0_49]),c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_51]),c_0_47]),c_0_48])]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
