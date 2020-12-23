%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 (1695 expanded)
%              Number of clauses        :   60 ( 680 expanded)
%              Number of leaves         :   13 ( 444 expanded)
%              Depth                    :   17
%              Number of atoms          :  419 (6444 expanded)
%              Number of equality atoms :   38 (1163 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   66 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r2_hidden(k2_xboole_0(X2,X3),X1)
               => k10_lattice3(k2_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_1)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(t1_yellow_1,axiom,(
    ! [X1] :
      ( u1_struct_0(k2_yellow_1(X1)) = X1
      & u1_orders_2(k2_yellow_1(X1)) = k1_yellow_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => ( r2_hidden(k2_xboole_0(X2,X3),X1)
                 => k10_lattice3(k2_yellow_1(X1),X2,X3) = k2_xboole_0(X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_yellow_1])).

fof(c_0_13,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
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

fof(c_0_14,plain,(
    ! [X25,X26,X27] :
      ( ( ~ r3_orders_2(k2_yellow_1(X25),X26,X27)
        | r1_tarski(X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))
        | ~ m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))
        | v1_xboole_0(X25) )
      & ( ~ r1_tarski(X26,X27)
        | r3_orders_2(k2_yellow_1(X25),X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))
        | ~ m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))
        | v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_15,plain,(
    ! [X24] :
      ( u1_struct_0(k2_yellow_1(X24)) = X24
      & u1_orders_2(k2_yellow_1(X24)) = k1_yellow_1(X24) ) ),
    inference(variable_rename,[status(thm)],[t1_yellow_1])).

fof(c_0_16,plain,(
    ! [X13,X14] :
      ( ~ r2_hidden(X13,X14)
      | m1_subset_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & r2_hidden(k2_xboole_0(esk2_0,esk3_0),esk1_0)
    & k10_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_18,plain,(
    ! [X1,X2,X3] :
      ( epred1_3(X3,X2,X1)
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
    inference(split_equiv,[status(thm)],[c_0_13])).

fof(c_0_19,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => epred1_3(X3,X2,X1) ) ) ) ),
    inference(apply_def,[status(thm)],[t18_yellow_0,c_0_13])).

fof(c_0_20,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r3_orders_2(X15,X16,X17)
        | r1_orders_2(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) )
      & ( ~ r1_orders_2(X15,X16,X17)
        | r3_orders_2(X15,X16,X17)
        | v2_struct_0(X15)
        | ~ v3_orders_2(X15)
        | ~ l1_orders_2(X15)
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | ~ m1_subset_1(X17,u1_struct_0(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_21,plain,(
    ! [X21] :
      ( v1_orders_2(k2_yellow_1(X21))
      & l1_orders_2(k2_yellow_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_22,plain,(
    ! [X22] :
      ( v1_orders_2(k2_yellow_1(X22))
      & v3_orders_2(k2_yellow_1(X22))
      & v4_orders_2(k2_yellow_1(X22))
      & v5_orders_2(k2_yellow_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

cnf(c_0_23,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( u1_struct_0(k2_yellow_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,plain,(
    ! [X31,X32,X33,X34,X35] :
      ( ( r1_orders_2(X31,X32,X34)
        | X34 != k10_lattice3(X31,X32,X33)
        | ~ r1_yellow_0(X31,k2_tarski(X32,X33))
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( r1_orders_2(X31,X33,X34)
        | X34 != k10_lattice3(X31,X32,X33)
        | ~ r1_yellow_0(X31,k2_tarski(X32,X33))
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( ~ m1_subset_1(X35,u1_struct_0(X31))
        | ~ r1_orders_2(X31,X32,X35)
        | ~ r1_orders_2(X31,X33,X35)
        | r1_orders_2(X31,X34,X35)
        | X34 != k10_lattice3(X31,X32,X33)
        | ~ r1_yellow_0(X31,k2_tarski(X32,X33))
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( X34 = k10_lattice3(X31,X32,X33)
        | m1_subset_1(esk4_4(X31,X32,X33,X34),u1_struct_0(X31))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( r1_yellow_0(X31,k2_tarski(X32,X33))
        | m1_subset_1(esk4_4(X31,X32,X33,X34),u1_struct_0(X31))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( X34 = k10_lattice3(X31,X32,X33)
        | r1_orders_2(X31,X32,esk4_4(X31,X32,X33,X34))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( r1_yellow_0(X31,k2_tarski(X32,X33))
        | r1_orders_2(X31,X32,esk4_4(X31,X32,X33,X34))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( X34 = k10_lattice3(X31,X32,X33)
        | r1_orders_2(X31,X33,esk4_4(X31,X32,X33,X34))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( r1_yellow_0(X31,k2_tarski(X32,X33))
        | r1_orders_2(X31,X33,esk4_4(X31,X32,X33,X34))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( X34 = k10_lattice3(X31,X32,X33)
        | ~ r1_orders_2(X31,X34,esk4_4(X31,X32,X33,X34))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) )
      & ( r1_yellow_0(X31,k2_tarski(X32,X33))
        | ~ r1_orders_2(X31,X34,esk4_4(X31,X32,X33,X34))
        | ~ r1_orders_2(X31,X32,X34)
        | ~ r1_orders_2(X31,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ epred1_3(X33,X32,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).

fof(c_0_28,plain,(
    ! [X18,X19,X20] :
      ( ~ v5_orders_2(X18)
      | ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | epred1_3(X20,X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_29,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k2_xboole_0(esk2_0,esk3_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_35,plain,(
    ! [X8,X9] : r1_tarski(X8,k2_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_36,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_37,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | m1_subset_1(esk4_4(X2,X3,X4,X1),u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( epred1_3(X3,X2,X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( r1_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_30]),c_0_31])])).

cnf(c_0_41,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X4,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_46,plain,
    ( X1 = k10_lattice3(k2_yellow_1(X2),X3,X4)
    | m1_subset_1(esk4_4(k2_yellow_1(X2),X3,X4,X1),X2)
    | ~ epred1_3(X4,X3,k2_yellow_1(X2))
    | ~ r1_orders_2(k2_yellow_1(X2),X4,X1)
    | ~ r1_orders_2(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_47,plain,
    ( epred1_3(X1,X2,k2_yellow_1(X3))
    | ~ m1_subset_1(X1,X3)
    | ~ m1_subset_1(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_39]),c_0_30])])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,plain,
    ( X1 = k10_lattice3(k2_yellow_1(X2),X3,X4)
    | r1_orders_2(k2_yellow_1(X2),X4,esk4_4(k2_yellow_1(X2),X3,X4,X1))
    | ~ epred1_3(X4,X3,k2_yellow_1(X2))
    | ~ r1_orders_2(k2_yellow_1(X2),X4,X1)
    | ~ r1_orders_2(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_24])).

cnf(c_0_53,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | r1_orders_2(X2,X3,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,plain,
    ( X1 = k10_lattice3(k2_yellow_1(X2),X3,X4)
    | m1_subset_1(esk4_4(k2_yellow_1(X2),X3,X4,X1),X2)
    | ~ r1_orders_2(k2_yellow_1(X2),X4,X1)
    | ~ r1_orders_2(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X3,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),esk3_0,k2_xboole_0(esk2_0,esk3_0))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_24])).

cnf(c_0_57,plain,
    ( X1 = k10_lattice3(k2_yellow_1(X2),X3,X4)
    | r1_orders_2(k2_yellow_1(X2),X4,esk4_4(k2_yellow_1(X2),X3,X4,X1))
    | ~ r1_orders_2(k2_yellow_1(X2),X4,X1)
    | ~ r1_orders_2(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X3,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_58,plain,
    ( X1 = k10_lattice3(k2_yellow_1(X2),X3,X4)
    | r1_orders_2(k2_yellow_1(X2),X3,esk4_4(k2_yellow_1(X2),X3,X4,X1))
    | ~ epred1_3(X4,X3,k2_yellow_1(X2))
    | ~ r1_orders_2(k2_yellow_1(X2),X4,X1)
    | ~ r1_orders_2(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk1_0),X1,esk3_0) = k2_xboole_0(esk2_0,esk3_0)
    | v2_struct_0(k2_yellow_1(esk1_0))
    | m1_subset_1(esk4_4(k2_yellow_1(esk1_0),X1,esk3_0,k2_xboole_0(esk2_0,esk3_0)),esk1_0)
    | ~ r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_33]),c_0_50])])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),esk2_0,k2_xboole_0(esk2_0,esk3_0))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_42]),c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0) != k2_xboole_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk1_0),X1,esk3_0) = k2_xboole_0(esk2_0,esk3_0)
    | r1_orders_2(k2_yellow_1(esk1_0),esk3_0,esk4_4(k2_yellow_1(esk1_0),X1,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_55]),c_0_33]),c_0_50])])).

cnf(c_0_64,plain,
    ( X1 = k10_lattice3(k2_yellow_1(X2),X3,X4)
    | r1_orders_2(k2_yellow_1(X2),X3,esk4_4(k2_yellow_1(X2),X3,X4,X1))
    | ~ r1_orders_2(k2_yellow_1(X2),X4,X1)
    | ~ r1_orders_2(k2_yellow_1(X2),X3,X1)
    | ~ m1_subset_1(X1,X2)
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X3,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk1_0))
    | m1_subset_1(esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_56])]),c_0_61])).

fof(c_0_66,plain,(
    ! [X10,X11,X12] :
      ( ~ r1_tarski(X10,X11)
      | ~ r1_tarski(X12,X11)
      | r1_tarski(k2_xboole_0(X10,X12),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_67,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,plain,
    ( r3_orders_2(k2_yellow_1(X1),X2,X3)
    | v2_struct_0(k2_yellow_1(X1))
    | ~ r1_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_24]),c_0_30]),c_0_31])])).

cnf(c_0_69,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),esk3_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_56])]),c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k10_lattice3(k2_yellow_1(esk1_0),X1,esk3_0) = k2_xboole_0(esk2_0,esk3_0)
    | r1_orders_2(k2_yellow_1(esk1_0),X1,esk4_4(k2_yellow_1(esk1_0),X1,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_55]),c_0_33]),c_0_50])])).

cnf(c_0_71,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r1_tarski(X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_65]),c_0_34])).

cnf(c_0_72,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_24]),c_0_24])).

cnf(c_0_74,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_50])]),c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),esk2_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_60]),c_0_56])]),c_0_61])).

cnf(c_0_76,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(X1,X2),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ m1_subset_1(k2_xboole_0(X1,X2),esk1_0)
    | ~ r1_tarski(X2,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk1_0))
    | r1_tarski(esk3_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_50])]),c_0_34]),c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_75]),c_0_56])]),c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(X1,esk3_0),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0))
    | ~ m1_subset_1(k2_xboole_0(X1,esk3_0),esk1_0)
    | ~ r1_tarski(X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(k2_yellow_1(esk1_0))
    | r1_tarski(esk2_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_78]),c_0_56])]),c_0_34]),c_0_65])).

cnf(c_0_81,negated_conjecture,
    ( r3_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_33])])).

fof(c_0_82,plain,(
    ! [X23] :
      ( ( ~ v2_struct_0(k2_yellow_1(X23))
        | v1_xboole_0(X23) )
      & ( v1_orders_2(k2_yellow_1(X23))
        | v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_83,plain,
    ( X1 = k10_lattice3(X2,X3,X4)
    | ~ r1_orders_2(X2,X1,esk4_4(X2,X3,X4,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_84,negated_conjecture,
    ( r1_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))
    | v2_struct_0(k2_yellow_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_81]),c_0_33])]),c_0_65])).

cnf(c_0_85,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_86,plain,
    ( v2_struct_0(k2_yellow_1(esk1_0))
    | ~ epred1_3(esk3_0,esk2_0,k2_yellow_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_24]),c_0_33])]),c_0_61]),c_0_60]),c_0_55])).

cnf(c_0_87,plain,
    ( ~ epred1_3(esk3_0,esk2_0,k2_yellow_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_34])).

cnf(c_0_88,plain,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_47]),c_0_50]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t8_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r2_hidden(k2_xboole_0(X2,X3),X1)=>k10_lattice3(k2_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_yellow_1)).
% 0.20/0.40  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.40  fof(t1_yellow_1, axiom, ![X1]:(u1_struct_0(k2_yellow_1(X1))=X1&u1_orders_2(k2_yellow_1(X1))=k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 0.20/0.40  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.40  fof(t18_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_0)).
% 0.20/0.40  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.20/0.40  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.40  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.40  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.40  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.40  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 0.20/0.40  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.20/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r2_hidden(k2_xboole_0(X2,X3),X1)=>k10_lattice3(k2_yellow_1(X1),X2,X3)=k2_xboole_0(X2,X3)))))), inference(assume_negation,[status(cth)],[t8_yellow_1])).
% 0.20/0.40  fof(c_0_13, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))), introduced(definition)).
% 0.20/0.40  fof(c_0_14, plain, ![X25, X26, X27]:((~r3_orders_2(k2_yellow_1(X25),X26,X27)|r1_tarski(X26,X27)|~m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))|~m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))|v1_xboole_0(X25))&(~r1_tarski(X26,X27)|r3_orders_2(k2_yellow_1(X25),X26,X27)|~m1_subset_1(X27,u1_struct_0(k2_yellow_1(X25)))|~m1_subset_1(X26,u1_struct_0(k2_yellow_1(X25)))|v1_xboole_0(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.20/0.40  fof(c_0_15, plain, ![X24]:(u1_struct_0(k2_yellow_1(X24))=X24&u1_orders_2(k2_yellow_1(X24))=k1_yellow_1(X24)), inference(variable_rename,[status(thm)],[t1_yellow_1])).
% 0.20/0.40  fof(c_0_16, plain, ![X13, X14]:(~r2_hidden(X13,X14)|m1_subset_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.40  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk1_0)&(m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))&(r2_hidden(k2_xboole_0(esk2_0,esk3_0),esk1_0)&k10_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.20/0.40  fof(c_0_18, plain, ![X1, X2, X3]:(epred1_3(X3,X2,X1)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3)))=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5)))))&(((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))=>(X4=k10_lattice3(X1,X2,X3)&r1_yellow_0(X1,k2_tarski(X2,X3))))))), inference(split_equiv,[status(thm)],[c_0_13])).
% 0.20/0.40  fof(c_0_19, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>epred1_3(X3,X2,X1)))), inference(apply_def,[status(thm)],[t18_yellow_0, c_0_13])).
% 0.20/0.40  fof(c_0_20, plain, ![X15, X16, X17]:((~r3_orders_2(X15,X16,X17)|r1_orders_2(X15,X16,X17)|(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))&(~r1_orders_2(X15,X16,X17)|r3_orders_2(X15,X16,X17)|(v2_struct_0(X15)|~v3_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,u1_struct_0(X15))|~m1_subset_1(X17,u1_struct_0(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.20/0.40  fof(c_0_21, plain, ![X21]:(v1_orders_2(k2_yellow_1(X21))&l1_orders_2(k2_yellow_1(X21))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.40  fof(c_0_22, plain, ![X22]:(((v1_orders_2(k2_yellow_1(X22))&v3_orders_2(k2_yellow_1(X22)))&v4_orders_2(k2_yellow_1(X22)))&v5_orders_2(k2_yellow_1(X22))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.40  cnf(c_0_23, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_24, plain, (u1_struct_0(k2_yellow_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_25, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r2_hidden(k2_xboole_0(esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_27, plain, ![X31, X32, X33, X34, X35]:((((r1_orders_2(X31,X32,X34)|(X34!=k10_lattice3(X31,X32,X33)|~r1_yellow_0(X31,k2_tarski(X32,X33)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31))&(r1_orders_2(X31,X33,X34)|(X34!=k10_lattice3(X31,X32,X33)|~r1_yellow_0(X31,k2_tarski(X32,X33)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31)))&(~m1_subset_1(X35,u1_struct_0(X31))|(~r1_orders_2(X31,X32,X35)|~r1_orders_2(X31,X33,X35)|r1_orders_2(X31,X34,X35))|(X34!=k10_lattice3(X31,X32,X33)|~r1_yellow_0(X31,k2_tarski(X32,X33)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31)))&(((X34=k10_lattice3(X31,X32,X33)|(m1_subset_1(esk4_4(X31,X32,X33,X34),u1_struct_0(X31))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31))&(r1_yellow_0(X31,k2_tarski(X32,X33))|(m1_subset_1(esk4_4(X31,X32,X33,X34),u1_struct_0(X31))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31)))&((((X34=k10_lattice3(X31,X32,X33)|(r1_orders_2(X31,X32,esk4_4(X31,X32,X33,X34))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31))&(r1_yellow_0(X31,k2_tarski(X32,X33))|(r1_orders_2(X31,X32,esk4_4(X31,X32,X33,X34))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31)))&((X34=k10_lattice3(X31,X32,X33)|(r1_orders_2(X31,X33,esk4_4(X31,X32,X33,X34))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31))&(r1_yellow_0(X31,k2_tarski(X32,X33))|(r1_orders_2(X31,X33,esk4_4(X31,X32,X33,X34))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31))))&((X34=k10_lattice3(X31,X32,X33)|(~r1_orders_2(X31,X34,esk4_4(X31,X32,X33,X34))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31))&(r1_yellow_0(X31,k2_tarski(X32,X33))|(~r1_orders_2(X31,X34,esk4_4(X31,X32,X33,X34))|(~r1_orders_2(X31,X32,X34)|~r1_orders_2(X31,X33,X34)))|~m1_subset_1(X34,u1_struct_0(X31))|~epred1_3(X33,X32,X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])])])).
% 0.20/0.40  fof(c_0_28, plain, ![X18, X19, X20]:(~v5_orders_2(X18)|~l1_orders_2(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~m1_subset_1(X20,u1_struct_0(X18))|epred1_3(X20,X19,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.40  cnf(c_0_29, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_30, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_31, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_32, plain, (v1_xboole_0(X1)|r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (m1_subset_1(k2_xboole_0(esk2_0,esk3_0),esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_35, plain, ![X8, X9]:r1_tarski(X8,k2_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.40  fof(c_0_36, plain, ![X6, X7]:k2_xboole_0(X6,X7)=k2_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.40  cnf(c_0_37, plain, (X1=k10_lattice3(X2,X3,X4)|m1_subset_1(esk4_4(X2,X3,X4,X1),u1_struct_0(X2))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_38, plain, (epred1_3(X3,X2,X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.40  cnf(c_0_39, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.40  cnf(c_0_40, plain, (r1_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_30]), c_0_31])])).
% 0.20/0.40  cnf(c_0_41, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.20/0.40  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_45, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X4,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_46, plain, (X1=k10_lattice3(k2_yellow_1(X2),X3,X4)|m1_subset_1(esk4_4(k2_yellow_1(X2),X3,X4,X1),X2)|~epred1_3(X4,X3,k2_yellow_1(X2))|~r1_orders_2(k2_yellow_1(X2),X4,X1)|~r1_orders_2(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 0.20/0.40  cnf(c_0_47, plain, (epred1_3(X1,X2,k2_yellow_1(X3))|~m1_subset_1(X1,X3)|~m1_subset_1(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_24]), c_0_39]), c_0_30])])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))|v2_struct_0(k2_yellow_1(esk1_0))|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,k2_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_33])])).
% 0.20/0.40  cnf(c_0_49, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_44, c_0_24])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_52, plain, (X1=k10_lattice3(k2_yellow_1(X2),X3,X4)|r1_orders_2(k2_yellow_1(X2),X4,esk4_4(k2_yellow_1(X2),X3,X4,X1))|~epred1_3(X4,X3,k2_yellow_1(X2))|~r1_orders_2(k2_yellow_1(X2),X4,X1)|~r1_orders_2(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_45, c_0_24])).
% 0.20/0.40  cnf(c_0_53, plain, (X1=k10_lattice3(X2,X3,X4)|r1_orders_2(X2,X3,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_54, plain, (X1=k10_lattice3(k2_yellow_1(X2),X3,X4)|m1_subset_1(esk4_4(k2_yellow_1(X2),X3,X4,X1),X2)|~r1_orders_2(k2_yellow_1(X2),X4,X1)|~r1_orders_2(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)|~m1_subset_1(X4,X2)|~m1_subset_1(X3,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),esk3_0,k2_xboole_0(esk2_0,esk3_0))|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_51, c_0_24])).
% 0.20/0.40  cnf(c_0_57, plain, (X1=k10_lattice3(k2_yellow_1(X2),X3,X4)|r1_orders_2(k2_yellow_1(X2),X4,esk4_4(k2_yellow_1(X2),X3,X4,X1))|~r1_orders_2(k2_yellow_1(X2),X4,X1)|~r1_orders_2(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)|~m1_subset_1(X4,X2)|~m1_subset_1(X3,X2)), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 0.20/0.40  cnf(c_0_58, plain, (X1=k10_lattice3(k2_yellow_1(X2),X3,X4)|r1_orders_2(k2_yellow_1(X2),X3,esk4_4(k2_yellow_1(X2),X3,X4,X1))|~epred1_3(X4,X3,k2_yellow_1(X2))|~r1_orders_2(k2_yellow_1(X2),X4,X1)|~r1_orders_2(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)), inference(spm,[status(thm)],[c_0_53, c_0_24])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (k10_lattice3(k2_yellow_1(esk1_0),X1,esk3_0)=k2_xboole_0(esk2_0,esk3_0)|v2_struct_0(k2_yellow_1(esk1_0))|m1_subset_1(esk4_4(k2_yellow_1(esk1_0),X1,esk3_0,k2_xboole_0(esk2_0,esk3_0)),esk1_0)|~r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_33]), c_0_50])])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),esk2_0,k2_xboole_0(esk2_0,esk3_0))|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_42]), c_0_56])])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (k10_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0)!=k2_xboole_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_62, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (k10_lattice3(k2_yellow_1(esk1_0),X1,esk3_0)=k2_xboole_0(esk2_0,esk3_0)|r1_orders_2(k2_yellow_1(esk1_0),esk3_0,esk4_4(k2_yellow_1(esk1_0),X1,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))|~r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_55]), c_0_33]), c_0_50])])).
% 0.20/0.40  cnf(c_0_64, plain, (X1=k10_lattice3(k2_yellow_1(X2),X3,X4)|r1_orders_2(k2_yellow_1(X2),X3,esk4_4(k2_yellow_1(X2),X3,X4,X1))|~r1_orders_2(k2_yellow_1(X2),X4,X1)|~r1_orders_2(k2_yellow_1(X2),X3,X1)|~m1_subset_1(X1,X2)|~m1_subset_1(X4,X2)|~m1_subset_1(X3,X2)), inference(spm,[status(thm)],[c_0_58, c_0_47])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (v2_struct_0(k2_yellow_1(esk1_0))|m1_subset_1(esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)),esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_56])]), c_0_61])).
% 0.20/0.40  fof(c_0_66, plain, ![X10, X11, X12]:(~r1_tarski(X10,X11)|~r1_tarski(X12,X11)|r1_tarski(k2_xboole_0(X10,X12),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 0.20/0.40  cnf(c_0_67, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_68, plain, (r3_orders_2(k2_yellow_1(X1),X2,X3)|v2_struct_0(k2_yellow_1(X1))|~r1_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_24]), c_0_30]), c_0_31])])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),esk3_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_60]), c_0_56])]), c_0_61])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (k10_lattice3(k2_yellow_1(esk1_0),X1,esk3_0)=k2_xboole_0(esk2_0,esk3_0)|r1_orders_2(k2_yellow_1(esk1_0),X1,esk4_4(k2_yellow_1(esk1_0),X1,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))|~r1_orders_2(k2_yellow_1(esk1_0),X1,k2_xboole_0(esk2_0,esk3_0))|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_55]), c_0_33]), c_0_50])])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))|~m1_subset_1(X1,esk1_0)|~r1_tarski(X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_65]), c_0_34])).
% 0.20/0.40  cnf(c_0_72, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.40  cnf(c_0_73, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_24]), c_0_24])).
% 0.20/0.40  cnf(c_0_74, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk3_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_50])]), c_0_65])).
% 0.20/0.40  cnf(c_0_75, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),esk2_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_60]), c_0_56])]), c_0_61])).
% 0.20/0.40  cnf(c_0_76, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(X1,X2),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))|~m1_subset_1(k2_xboole_0(X1,X2),esk1_0)|~r1_tarski(X2,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|~r1_tarski(X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.40  cnf(c_0_77, negated_conjecture, (v2_struct_0(k2_yellow_1(esk1_0))|r1_tarski(esk3_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_50])]), c_0_34]), c_0_65])).
% 0.20/0.40  cnf(c_0_78, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),esk2_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_75]), c_0_56])]), c_0_65])).
% 0.20/0.40  cnf(c_0_79, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(X1,esk3_0),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))|~m1_subset_1(k2_xboole_0(X1,esk3_0),esk1_0)|~r1_tarski(X1,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.40  cnf(c_0_80, negated_conjecture, (v2_struct_0(k2_yellow_1(esk1_0))|r1_tarski(esk2_0,esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_78]), c_0_56])]), c_0_34]), c_0_65])).
% 0.20/0.40  cnf(c_0_81, negated_conjecture, (r3_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_33])])).
% 0.20/0.40  fof(c_0_82, plain, ![X23]:((~v2_struct_0(k2_yellow_1(X23))|v1_xboole_0(X23))&(v1_orders_2(k2_yellow_1(X23))|v1_xboole_0(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.20/0.40  cnf(c_0_83, plain, (X1=k10_lattice3(X2,X3,X4)|~r1_orders_2(X2,X1,esk4_4(X2,X3,X4,X1))|~r1_orders_2(X2,X3,X1)|~r1_orders_2(X2,X4,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~epred1_3(X4,X3,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_84, negated_conjecture, (r1_orders_2(k2_yellow_1(esk1_0),k2_xboole_0(esk2_0,esk3_0),esk4_4(k2_yellow_1(esk1_0),esk2_0,esk3_0,k2_xboole_0(esk2_0,esk3_0)))|v2_struct_0(k2_yellow_1(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_81]), c_0_33])]), c_0_65])).
% 0.20/0.40  cnf(c_0_85, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.40  cnf(c_0_86, plain, (v2_struct_0(k2_yellow_1(esk1_0))|~epred1_3(esk3_0,esk2_0,k2_yellow_1(esk1_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_24]), c_0_33])]), c_0_61]), c_0_60]), c_0_55])).
% 0.20/0.40  cnf(c_0_87, plain, (~epred1_3(esk3_0,esk2_0,k2_yellow_1(esk1_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_34])).
% 0.20/0.40  cnf(c_0_88, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_47]), c_0_50]), c_0_56])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 89
% 0.20/0.40  # Proof object clause steps            : 60
% 0.20/0.40  # Proof object formula steps           : 29
% 0.20/0.40  # Proof object conjectures             : 30
% 0.20/0.40  # Proof object clause conjectures      : 27
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 23
% 0.20/0.40  # Proof object initial formulas used   : 12
% 0.20/0.40  # Proof object generating inferences   : 33
% 0.20/0.40  # Proof object simplifying inferences  : 70
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 12
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 35
% 0.20/0.40  # Removed in clause preprocessing      : 1
% 0.20/0.40  # Initial clauses in saturation        : 34
% 0.20/0.40  # Processed clauses                    : 241
% 0.20/0.40  # ...of these trivial                  : 3
% 0.20/0.40  # ...subsumed                          : 36
% 0.20/0.40  # ...remaining for further processing  : 202
% 0.20/0.40  # Other redundant clauses eliminated   : 3
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 0
% 0.20/0.40  # Backward-rewritten                   : 2
% 0.20/0.40  # Generated clauses                    : 272
% 0.20/0.40  # ...of the previous two non-trivial   : 266
% 0.20/0.40  # Contextual simplify-reflections      : 14
% 0.20/0.40  # Paramodulations                      : 269
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 3
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 165
% 0.20/0.40  #    Positive orientable unit clauses  : 12
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 149
% 0.20/0.40  # Current number of unprocessed clauses: 91
% 0.20/0.40  # ...number of literals in the above   : 524
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 35
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 4676
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1212
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 50
% 0.20/0.40  # Unit Clause-clause subsumption calls : 26
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 10
% 0.20/0.40  # BW rewrite match successes           : 9
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 14242
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
