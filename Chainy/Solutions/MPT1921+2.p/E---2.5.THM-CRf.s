%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1921+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:09 EST 2020

% Result     : Theorem 10.24s
% Output     : CNFRefutation 10.24s
% Verified   : 
% Statistics : Number of formulae       :   27 (  44 expanded)
%              Number of clauses        :   14 (  16 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  105 ( 167 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_yellow_6)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(t19_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_6)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT025+2.ax',d13_yellow_0)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT025+2.ax',dt_m1_yellow_0)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT027+2.ax',dt_l1_waybel_0)).

fof(c_0_6,plain,(
    ! [X12151,X12152,X12153] :
      ( ( m1_yellow_0(X12153,X12152)
        | ~ m1_yellow_6(X12153,X12151,X12152)
        | ~ l1_waybel_0(X12153,X12151)
        | ~ l1_waybel_0(X12152,X12151)
        | ~ l1_struct_0(X12151) )
      & ( u1_waybel_0(X12151,X12153) = k2_partfun1(u1_struct_0(X12152),u1_struct_0(X12151),u1_waybel_0(X12151,X12152),u1_struct_0(X12153))
        | ~ m1_yellow_6(X12153,X12151,X12152)
        | ~ l1_waybel_0(X12153,X12151)
        | ~ l1_waybel_0(X12152,X12151)
        | ~ l1_struct_0(X12151) )
      & ( ~ m1_yellow_0(X12153,X12152)
        | u1_waybel_0(X12151,X12153) != k2_partfun1(u1_struct_0(X12152),u1_struct_0(X12151),u1_waybel_0(X12151,X12152),u1_struct_0(X12153))
        | m1_yellow_6(X12153,X12151,X12152)
        | ~ l1_waybel_0(X12153,X12151)
        | ~ l1_waybel_0(X12152,X12151)
        | ~ l1_struct_0(X12151) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

fof(c_0_7,plain,(
    ! [X12168,X12169,X12170] :
      ( ~ l1_struct_0(X12168)
      | ~ l1_waybel_0(X12169,X12168)
      | ~ m1_yellow_6(X12170,X12168,X12169)
      | l1_waybel_0(X12170,X12168) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_waybel_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_6(X3,X1,X2)
               => r1_tarski(u1_struct_0(X3),u1_struct_0(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t19_yellow_6])).

fof(c_0_9,plain,(
    ! [X9469,X9470] :
      ( ( r1_tarski(u1_struct_0(X9470),u1_struct_0(X9469))
        | ~ m1_yellow_0(X9470,X9469)
        | ~ l1_orders_2(X9470)
        | ~ l1_orders_2(X9469) )
      & ( r1_tarski(u1_orders_2(X9470),u1_orders_2(X9469))
        | ~ m1_yellow_0(X9470,X9469)
        | ~ l1_orders_2(X9470)
        | ~ l1_orders_2(X9469) )
      & ( ~ r1_tarski(u1_struct_0(X9470),u1_struct_0(X9469))
        | ~ r1_tarski(u1_orders_2(X9470),u1_orders_2(X9469))
        | m1_yellow_0(X9470,X9469)
        | ~ l1_orders_2(X9470)
        | ~ l1_orders_2(X9469) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_10,plain,(
    ! [X9529,X9530] :
      ( ~ l1_orders_2(X9529)
      | ~ m1_yellow_0(X9530,X9529)
      | l1_orders_2(X9530) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_11,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,negated_conjecture,
    ( l1_struct_0(esk1422_0)
    & l1_waybel_0(esk1423_0,esk1422_0)
    & m1_yellow_6(esk1424_0,esk1422_0,esk1423_0)
    & ~ r1_tarski(u1_struct_0(esk1424_0),u1_struct_0(esk1423_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_14,plain,(
    ! [X10148,X10149] :
      ( ~ l1_struct_0(X10148)
      | ~ l1_waybel_0(X10149,X10148)
      | l1_orders_2(X10149) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_15,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_yellow_6(esk1424_0,esk1422_0,esk1423_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_waybel_0(esk1423_0,esk1422_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_struct_0(esk1422_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_yellow_0(esk1424_0,esk1423_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk1423_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(esk1424_0),u1_struct_0(esk1423_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),c_0_25]),
    [proof]).
%------------------------------------------------------------------------------
