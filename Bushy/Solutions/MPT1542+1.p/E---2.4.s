%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t20_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:38 EDT 2019

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   67 (1196 expanded)
%              Number of clauses        :   54 ( 426 expanded)
%              Number of leaves         :    5 ( 298 expanded)
%              Depth                    :   16
%              Number of atoms          :  499 (12226 expanded)
%              Number of equality atoms :   16 ( 432 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal clause size      :   66 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( ( X4 = k10_lattice3(X1,X2,X3)
                        & r1_yellow_0(X1,k2_tarski(X2,X3)) )
                     => ( r1_orders_2(X1,X2,X4)
                        & r1_orders_2(X1,X3,X4)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X2,X5)
                                & r1_orders_2(X1,X3,X5) )
                             => r1_orders_2(X1,X4,X5) ) ) ) )
                    & ( ( r1_orders_2(X1,X2,X4)
                        & r1_orders_2(X1,X3,X4)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_orders_2(X1,X2,X5)
                                & r1_orders_2(X1,X3,X5) )
                             => r1_orders_2(X1,X4,X5) ) ) )
                     => ( X4 = k10_lattice3(X1,X2,X3)
                        & r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t20_yellow_0.p',t18_yellow_0)).

fof(t20_yellow_0,conjecture,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t20_yellow_0.p',t20_yellow_0)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t20_yellow_0.p',dt_k10_lattice3)).

fof(d10_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                    & r1_orders_2(X1,X2,X4)
                    & r1_orders_2(X1,X3,X4)
                    & ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ( ( r1_orders_2(X1,X2,X5)
                            & r1_orders_2(X1,X3,X5) )
                         => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t20_yellow_0.p',d10_lattice3)).

fof(c_0_4,plain,(
    ! [X3,X2,X1] :
      ( epred1_3(X1,X2,X3)
    <=> ! [X4] :
          ( m1_subset_1(X4,u1_struct_0(X1))
         => ( ( ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) )
             => ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) ) )
            & ( ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) )
             => ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ) ),
    introduced(definition)).

fof(c_0_5,plain,(
    ! [X3,X2,X1] :
      ( epred1_3(X1,X2,X3)
     => ! [X4] :
          ( m1_subset_1(X4,u1_struct_0(X1))
         => ( ( ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) )
             => ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) ) )
            & ( ( r1_orders_2(X1,X2,X4)
                & r1_orders_2(X1,X3,X4)
                & ! [X5] :
                    ( m1_subset_1(X5,u1_struct_0(X1))
                   => ( ( r1_orders_2(X1,X2,X5)
                        & r1_orders_2(X1,X3,X5) )
                     => r1_orders_2(X1,X4,X5) ) ) )
             => ( X4 = k10_lattice3(X1,X2,X3)
                & r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_4])).

fof(c_0_6,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ( r1_orders_2(X46,X45,X47)
        | X47 != k10_lattice3(X46,X45,X44)
        | ~ r1_yellow_0(X46,k2_tarski(X45,X44))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( r1_orders_2(X46,X44,X47)
        | X47 != k10_lattice3(X46,X45,X44)
        | ~ r1_yellow_0(X46,k2_tarski(X45,X44))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ r1_orders_2(X46,X45,X48)
        | ~ r1_orders_2(X46,X44,X48)
        | r1_orders_2(X46,X47,X48)
        | X47 != k10_lattice3(X46,X45,X44)
        | ~ r1_yellow_0(X46,k2_tarski(X45,X44))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( X47 = k10_lattice3(X46,X45,X44)
        | m1_subset_1(esk11_4(X44,X45,X46,X47),u1_struct_0(X46))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( r1_yellow_0(X46,k2_tarski(X45,X44))
        | m1_subset_1(esk11_4(X44,X45,X46,X47),u1_struct_0(X46))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( X47 = k10_lattice3(X46,X45,X44)
        | r1_orders_2(X46,X45,esk11_4(X44,X45,X46,X47))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( r1_yellow_0(X46,k2_tarski(X45,X44))
        | r1_orders_2(X46,X45,esk11_4(X44,X45,X46,X47))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( X47 = k10_lattice3(X46,X45,X44)
        | r1_orders_2(X46,X44,esk11_4(X44,X45,X46,X47))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( r1_yellow_0(X46,k2_tarski(X45,X44))
        | r1_orders_2(X46,X44,esk11_4(X44,X45,X46,X47))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( X47 = k10_lattice3(X46,X45,X44)
        | ~ r1_orders_2(X46,X47,esk11_4(X44,X45,X46,X47))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) )
      & ( r1_yellow_0(X46,k2_tarski(X45,X44))
        | ~ r1_orders_2(X46,X47,esk11_4(X44,X45,X46,X47))
        | ~ r1_orders_2(X46,X45,X47)
        | ~ r1_orders_2(X46,X44,X47)
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | ~ epred1_3(X46,X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])])).

fof(c_0_7,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => epred1_3(X1,X2,X3) ) ) ) ),
    inference(apply_def,[status(thm)],[t18_yellow_0,c_0_4])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v1_lattice3(X1)
        <=> ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_yellow_0])).

cnf(c_0_9,plain,
    ( r1_orders_2(X2,X5,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k10_lattice3(X2,X3,X4)
    | ~ r1_yellow_0(X2,k2_tarski(X3,X4))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ epred1_3(X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | ~ m1_subset_1(X26,u1_struct_0(X24))
      | m1_subset_1(k10_lattice3(X24,X25,X26),u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

fof(c_0_11,plain,(
    ! [X32,X33,X34] :
      ( ~ v5_orders_2(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_subset_1(X33,u1_struct_0(X32))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | epred1_3(X32,X33,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_12,negated_conjecture,(
    ! [X9,X10] :
      ( v5_orders_2(esk1_0)
      & l1_orders_2(esk1_0)
      & ( m1_subset_1(esk2_0,u1_struct_0(esk1_0))
        | ~ v1_lattice3(esk1_0) )
      & ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
        | ~ v1_lattice3(esk1_0) )
      & ( ~ r1_yellow_0(esk1_0,k2_tarski(esk2_0,esk3_0))
        | ~ v1_lattice3(esk1_0) )
      & ( v1_lattice3(esk1_0)
        | ~ m1_subset_1(X9,u1_struct_0(esk1_0))
        | ~ m1_subset_1(X10,u1_struct_0(esk1_0))
        | r1_yellow_0(esk1_0,k2_tarski(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( epred1_3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X15,X16,X17,X19,X22] :
      ( ( m1_subset_1(esk4_3(X15,X16,X17),u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X16,esk4_3(X15,X16,X17))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,X17,esk4_3(X15,X16,X17))
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ m1_subset_1(X19,u1_struct_0(X15))
        | ~ r1_orders_2(X15,X16,X19)
        | ~ r1_orders_2(X15,X17,X19)
        | r1_orders_2(X15,esk4_3(X15,X16,X17),X19)
        | ~ m1_subset_1(X17,u1_struct_0(X15))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk5_1(X15),u1_struct_0(X15))
        | v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk6_1(X15),u1_struct_0(X15))
        | v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( m1_subset_1(esk7_2(X15,X22),u1_struct_0(X15))
        | ~ m1_subset_1(X22,u1_struct_0(X15))
        | ~ r1_orders_2(X15,esk5_1(X15),X22)
        | ~ r1_orders_2(X15,esk6_1(X15),X22)
        | v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,esk5_1(X15),esk7_2(X15,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X15))
        | ~ r1_orders_2(X15,esk5_1(X15),X22)
        | ~ r1_orders_2(X15,esk6_1(X15),X22)
        | v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( r1_orders_2(X15,esk6_1(X15),esk7_2(X15,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X15))
        | ~ r1_orders_2(X15,esk5_1(X15),X22)
        | ~ r1_orders_2(X15,esk6_1(X15),X22)
        | v1_lattice3(X15)
        | ~ l1_orders_2(X15) )
      & ( ~ r1_orders_2(X15,X22,esk7_2(X15,X22))
        | ~ m1_subset_1(X22,u1_struct_0(X15))
        | ~ r1_orders_2(X15,esk5_1(X15),X22)
        | ~ r1_orders_2(X15,esk6_1(X15),X22)
        | v1_lattice3(X15)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_lattice3])])])])])).

cnf(c_0_19,plain,
    ( r1_orders_2(X1,k10_lattice3(X1,X2,X3),X4)
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_lattice3(esk1_0)
    | r1_yellow_0(esk1_0,k2_tarski(X1,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( epred1_3(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X4,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X4,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X1,X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( v1_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk7_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk5_1(X1),X2)
    | ~ r1_orders_2(X1,esk6_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_orders_2(esk1_0,k10_lattice3(esk1_0,X1,X2),X3)
    | v1_lattice3(esk1_0)
    | ~ r1_orders_2(esk1_0,X2,X3)
    | ~ r1_orders_2(esk1_0,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17])]),c_0_21])).

cnf(c_0_25,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X1,X3,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(k10_lattice3(X1,X3,X2),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( r1_orders_2(X1,X2,X3)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ epred1_3(X1,X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,negated_conjecture,
    ( v1_lattice3(esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk7_2(esk1_0,k10_lattice3(esk1_0,X2,X1)))
    | ~ r1_orders_2(esk1_0,X2,esk7_2(esk1_0,k10_lattice3(esk1_0,X2,X1)))
    | ~ r1_orders_2(esk1_0,esk5_1(esk1_0),k10_lattice3(esk1_0,X2,X1))
    | ~ r1_orders_2(esk1_0,esk6_1(esk1_0),k10_lattice3(esk1_0,X2,X1))
    | ~ m1_subset_1(esk7_2(esk1_0,k10_lattice3(esk1_0,X2,X1)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k10_lattice3(esk1_0,X2,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_17])])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk5_1(X1),X2)
    | ~ r1_orders_2(X1,esk6_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X3,X2))
    | ~ epred1_3(X1,X3,X2)
    | ~ r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_lattice3(esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk7_2(esk1_0,k10_lattice3(esk1_0,X2,X1)))
    | ~ r1_orders_2(esk1_0,X2,esk7_2(esk1_0,k10_lattice3(esk1_0,X2,X1)))
    | ~ r1_orders_2(esk1_0,esk5_1(esk1_0),k10_lattice3(esk1_0,X2,X1))
    | ~ r1_orders_2(esk1_0,esk6_1(esk1_0),k10_lattice3(esk1_0,X2,X1))
    | ~ m1_subset_1(k10_lattice3(esk1_0,X2,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_17])])).

cnf(c_0_32,plain,
    ( r1_orders_2(X1,esk6_1(X1),esk7_2(X1,X2))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk5_1(X1),X2)
    | ~ r1_orders_2(X1,esk6_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,k10_lattice3(esk1_0,X2,X1))
    | v1_lattice3(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_17])]),c_0_21])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( v1_lattice3(esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk7_2(esk1_0,k10_lattice3(esk1_0,X1,esk6_1(esk1_0))))
    | ~ r1_orders_2(esk1_0,esk5_1(esk1_0),k10_lattice3(esk1_0,X1,esk6_1(esk1_0)))
    | ~ m1_subset_1(k10_lattice3(esk1_0,X1,esk6_1(esk1_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_1(esk1_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])]),c_0_33])).

cnf(c_0_36,plain,
    ( r1_orders_2(X1,esk5_1(X1),esk7_2(X1,X2))
    | v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r1_orders_2(X1,esk5_1(X1),X2)
    | ~ r1_orders_2(X1,esk6_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,k10_lattice3(esk1_0,X1,X2))
    | v1_lattice3(esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_17])]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v1_lattice3(esk1_0)
    | ~ m1_subset_1(k10_lattice3(esk1_0,esk5_1(esk1_0),esk6_1(esk1_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk6_1(esk1_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk5_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_17])]),c_0_33]),c_0_37])).

cnf(c_0_39,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ r1_orders_2(X1,X4,esk11_4(X3,X2,X1,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_40,plain,
    ( r1_orders_2(X2,esk4_3(X2,X3,X4),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_42,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk11_4(X3,X2,X1,X4),u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_43,negated_conjecture,
    ( v1_lattice3(esk1_0)
    | ~ m1_subset_1(esk6_1(esk1_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(esk5_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_14]),c_0_17])])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk6_1(X1),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,esk11_4(X3,X2,X1,esk4_3(X1,X5,X4)))
    | ~ r1_orders_2(X1,X5,esk11_4(X3,X2,X1,esk4_3(X1,X5,X4)))
    | ~ r1_orders_2(X1,X3,esk4_3(X1,X5,X4))
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X5,X4))
    | ~ m1_subset_1(esk11_4(X3,X2,X1,esk4_3(X1,X5,X4)),u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | m1_subset_1(esk11_4(X3,X2,X1,esk4_3(X1,X4,X5)),u1_struct_0(X1))
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,esk4_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_47,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X3,esk11_4(X3,X2,X1,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_48,negated_conjecture,
    ( v1_lattice3(esk1_0)
    | ~ m1_subset_1(esk5_1(esk1_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_17])])).

cnf(c_0_49,plain,
    ( m1_subset_1(esk5_1(X1),u1_struct_0(X1))
    | v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_50,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,esk11_4(X3,X2,X1,esk4_3(X1,X5,X4)))
    | ~ r1_orders_2(X1,X5,esk11_4(X3,X2,X1,esk4_3(X1,X5,X4)))
    | ~ r1_orders_2(X1,X3,esk4_3(X1,X5,X4))
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X5,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r1_orders_2(X1,X2,esk11_4(X2,X3,X1,esk4_3(X1,X4,X5)))
    | r1_yellow_0(X1,k2_tarski(X3,X2))
    | ~ epred1_3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X3,esk4_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_52,plain,
    ( r1_orders_2(X1,X2,esk4_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_53,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,X2,esk11_4(X3,X2,X1,X4))
    | ~ r1_orders_2(X1,X2,X4)
    | ~ r1_orders_2(X1,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,k2_tarski(esk2_0,esk3_0))
    | ~ v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_55,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_17])])).

cnf(c_0_56,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_orders_2(X1,X4,esk11_4(X3,X2,X1,esk4_3(X1,X4,X3)))
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X4,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_57,plain,
    ( r1_orders_2(X1,X2,esk11_4(X3,X2,X1,esk4_3(X1,X4,X5)))
    | r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,esk4_3(X1,X4,X5))
    | ~ r1_orders_2(X1,X2,esk4_3(X1,X4,X5))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_41])).

cnf(c_0_58,plain,
    ( r1_orders_2(X1,X2,esk4_3(X1,X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    | ~ v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    | ~ v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_yellow_0(esk1_0,k2_tarski(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_62,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ epred1_3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_52]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_55])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_55])])).

cnf(c_0_65,negated_conjecture,
    ( ~ epred1_3(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_55]),c_0_17])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_21]),c_0_63]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
