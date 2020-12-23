%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1625+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 36.33s
% Output     : CNFRefutation 36.33s
% Verified   : 
% Statistics : Number of formulae       :  100 (1750 expanded)
%              Number of clauses        :   59 ( 653 expanded)
%              Number of leaves         :   20 ( 465 expanded)
%              Depth                    :   14
%              Number of atoms          :  502 (6602 expanded)
%              Number of equality atoms :  117 ( 821 expanded)
%              Maximal formula depth    :   47 (   5 average)
%              Maximal clause size      :   68 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1)
            & v2_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',dt_l1_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',t75_enumset1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(t7_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X2,X3) )
                & ( r1_orders_2(X1,X2,X3)
                 => r1_lattice3(X1,k1_tarski(X3),X2) )
                & ( r2_lattice3(X1,k1_tarski(X3),X2)
                 => r1_orders_2(X1,X3,X2) )
                & ( r1_orders_2(X1,X3,X2)
                 => r2_lattice3(X1,k1_tarski(X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT025+2.ax',t7_yellow_0)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',t24_orders_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',dt_k6_domain_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT006+2.ax',t4_subset)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT003+2.ax',d2_tarski)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT024+2.ax',d9_lattice3)).

fof(d1_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X3,X5)
                                & r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_0)).

fof(d6_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8,X9] :
      ( X9 = k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X10] :
          ( r2_hidden(X10,X9)
        <=> ~ ( X10 != X1
              & X10 != X2
              & X10 != X3
              & X10 != X4
              & X10 != X5
              & X10 != X6
              & X10 != X7
              & X10 != X8 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT005+2.ax',d6_enumset1)).

fof(d2_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X5,X3)
                                & r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1)
              & v2_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_0])).

fof(c_0_21,plain,(
    ! [X6188] :
      ( ~ l1_orders_2(X6188)
      | l1_struct_0(X6188) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1154_0)
    & v3_orders_2(esk1154_0)
    & l1_orders_2(esk1154_0)
    & m1_subset_1(esk1155_0,u1_struct_0(esk1154_0))
    & ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
      | ~ v2_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X6298,X6299] :
      ( v1_xboole_0(X6298)
      | ~ m1_subset_1(X6299,X6298)
      | k6_domain_1(X6298,X6299) = k1_tarski(X6299) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_24,plain,(
    ! [X899] : k2_tarski(X899,X899) = k1_tarski(X899) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_25,plain,(
    ! [X900,X901] : k1_enumset1(X900,X900,X901) = k2_tarski(X900,X901) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_26,plain,(
    ! [X902,X903,X904] : k2_enumset1(X902,X902,X903,X904) = k1_enumset1(X902,X903,X904) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X905,X906,X907,X908] : k3_enumset1(X905,X905,X906,X907,X908) = k2_enumset1(X905,X906,X907,X908) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X909,X910,X911,X912,X913] : k4_enumset1(X909,X909,X910,X911,X912,X913) = k3_enumset1(X909,X910,X911,X912,X913) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X914,X915,X916,X917,X918,X919] : k5_enumset1(X914,X914,X915,X916,X917,X918,X919) = k4_enumset1(X914,X915,X916,X917,X918,X919) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X920,X921,X922,X923,X924,X925,X926] : k6_enumset1(X920,X920,X921,X922,X923,X924,X925,X926) = k5_enumset1(X920,X921,X922,X923,X924,X925,X926) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_32,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( l1_orders_2(esk1154_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X9799,X9800,X9801] :
      ( ( ~ r1_lattice3(X9799,k1_tarski(X9801),X9800)
        | r1_orders_2(X9799,X9800,X9801)
        | ~ m1_subset_1(X9801,u1_struct_0(X9799))
        | ~ m1_subset_1(X9800,u1_struct_0(X9799))
        | ~ l1_orders_2(X9799) )
      & ( ~ r1_orders_2(X9799,X9800,X9801)
        | r1_lattice3(X9799,k1_tarski(X9801),X9800)
        | ~ m1_subset_1(X9801,u1_struct_0(X9799))
        | ~ m1_subset_1(X9800,u1_struct_0(X9799))
        | ~ l1_orders_2(X9799) )
      & ( ~ r2_lattice3(X9799,k1_tarski(X9801),X9800)
        | r1_orders_2(X9799,X9801,X9800)
        | ~ m1_subset_1(X9801,u1_struct_0(X9799))
        | ~ m1_subset_1(X9800,u1_struct_0(X9799))
        | ~ l1_orders_2(X9799) )
      & ( ~ r1_orders_2(X9799,X9801,X9800)
        | r2_lattice3(X9799,k1_tarski(X9801),X9800)
        | ~ m1_subset_1(X9801,u1_struct_0(X9799))
        | ~ m1_subset_1(X9800,u1_struct_0(X9799))
        | ~ l1_orders_2(X9799) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

fof(c_0_35,plain,(
    ! [X6351,X6352] :
      ( v2_struct_0(X6351)
      | ~ v3_orders_2(X6351)
      | ~ l1_orders_2(X6351)
      | ~ m1_subset_1(X6352,u1_struct_0(X6351))
      | r1_orders_2(X6351,X6352,X6352) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( l1_struct_0(esk1154_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk1154_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_47,plain,(
    ! [X6183,X6184] :
      ( v1_xboole_0(X6183)
      | ~ m1_subset_1(X6184,X6183)
      | m1_subset_1(k6_domain_1(X6183,X6184),k1_zfmisc_1(X6183)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_48,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk1155_0,u1_struct_0(esk1154_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( v3_orders_2(esk1154_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_52,plain,
    ( k6_domain_1(X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1154_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

fof(c_0_54,plain,(
    ! [X2040,X2041,X2042] :
      ( ~ r2_hidden(X2040,X2041)
      | ~ m1_subset_1(X2041,k1_zfmisc_1(X2042))
      | m1_subset_1(X2040,X2042) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_56,plain,(
    ! [X469,X470,X471,X472,X473,X474,X475,X476] :
      ( ( ~ r2_hidden(X472,X471)
        | X472 = X469
        | X472 = X470
        | X471 != k2_tarski(X469,X470) )
      & ( X473 != X469
        | r2_hidden(X473,X471)
        | X471 != k2_tarski(X469,X470) )
      & ( X473 != X470
        | r2_hidden(X473,X471)
        | X471 != k2_tarski(X469,X470) )
      & ( esk18_3(X474,X475,X476) != X474
        | ~ r2_hidden(esk18_3(X474,X475,X476),X476)
        | X476 = k2_tarski(X474,X475) )
      & ( esk18_3(X474,X475,X476) != X475
        | ~ r2_hidden(esk18_3(X474,X475,X476),X476)
        | X476 = k2_tarski(X474,X475) )
      & ( r2_hidden(esk18_3(X474,X475,X476),X476)
        | esk18_3(X474,X475,X476) = X474
        | esk18_3(X474,X475,X476) = X475
        | X476 = k2_tarski(X474,X475) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_57,plain,(
    ! [X8954,X8955,X8956,X8957] :
      ( ( ~ r2_lattice3(X8954,X8955,X8956)
        | ~ m1_subset_1(X8957,u1_struct_0(X8954))
        | ~ r2_hidden(X8957,X8955)
        | r1_orders_2(X8954,X8957,X8956)
        | ~ m1_subset_1(X8956,u1_struct_0(X8954))
        | ~ l1_orders_2(X8954) )
      & ( m1_subset_1(esk995_3(X8954,X8955,X8956),u1_struct_0(X8954))
        | r2_lattice3(X8954,X8955,X8956)
        | ~ m1_subset_1(X8956,u1_struct_0(X8954))
        | ~ l1_orders_2(X8954) )
      & ( r2_hidden(esk995_3(X8954,X8955,X8956),X8955)
        | r2_lattice3(X8954,X8955,X8956)
        | ~ m1_subset_1(X8956,u1_struct_0(X8954))
        | ~ l1_orders_2(X8954) )
      & ( ~ r1_orders_2(X8954,esk995_3(X8954,X8955,X8956),X8956)
        | r2_lattice3(X8954,X8955,X8956)
        | ~ m1_subset_1(X8956,u1_struct_0(X8954))
        | ~ l1_orders_2(X8954) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_58,plain,
    ( r2_lattice3(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)
    | ~ l1_orders_2(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_59,negated_conjecture,
    ( r1_orders_2(esk1154_0,esk1155_0,esk1155_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_33])]),c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( k6_enumset1(esk1155_0,esk1155_0,esk1155_0,esk1155_0,esk1155_0,esk1155_0,esk1155_0,esk1155_0) = k6_domain_1(u1_struct_0(esk1154_0),esk1155_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_50]),c_0_53])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),k1_zfmisc_1(u1_struct_0(esk1154_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_53])).

fof(c_0_63,plain,(
    ! [X9964,X9965,X9966,X9967,X9971] :
      ( ( m1_subset_1(esk1135_4(X9964,X9965,X9966,X9967),u1_struct_0(X9964))
        | ~ r2_hidden(X9966,X9965)
        | ~ r2_hidden(X9967,X9965)
        | ~ m1_subset_1(X9967,u1_struct_0(X9964))
        | ~ m1_subset_1(X9966,u1_struct_0(X9964))
        | ~ v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( r2_hidden(esk1135_4(X9964,X9965,X9966,X9967),X9965)
        | ~ r2_hidden(X9966,X9965)
        | ~ r2_hidden(X9967,X9965)
        | ~ m1_subset_1(X9967,u1_struct_0(X9964))
        | ~ m1_subset_1(X9966,u1_struct_0(X9964))
        | ~ v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( r1_orders_2(X9964,X9966,esk1135_4(X9964,X9965,X9966,X9967))
        | ~ r2_hidden(X9966,X9965)
        | ~ r2_hidden(X9967,X9965)
        | ~ m1_subset_1(X9967,u1_struct_0(X9964))
        | ~ m1_subset_1(X9966,u1_struct_0(X9964))
        | ~ v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( r1_orders_2(X9964,X9967,esk1135_4(X9964,X9965,X9966,X9967))
        | ~ r2_hidden(X9966,X9965)
        | ~ r2_hidden(X9967,X9965)
        | ~ m1_subset_1(X9967,u1_struct_0(X9964))
        | ~ m1_subset_1(X9966,u1_struct_0(X9964))
        | ~ v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( m1_subset_1(esk1136_2(X9964,X9965),u1_struct_0(X9964))
        | v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( m1_subset_1(esk1137_2(X9964,X9965),u1_struct_0(X9964))
        | v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( r2_hidden(esk1136_2(X9964,X9965),X9965)
        | v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( r2_hidden(esk1137_2(X9964,X9965),X9965)
        | v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) )
      & ( ~ m1_subset_1(X9971,u1_struct_0(X9964))
        | ~ r2_hidden(X9971,X9965)
        | ~ r1_orders_2(X9964,esk1136_2(X9964,X9965),X9971)
        | ~ r1_orders_2(X9964,esk1137_2(X9964,X9965),X9971)
        | v1_waybel_0(X9965,X9964)
        | ~ m1_subset_1(X9965,k1_zfmisc_1(u1_struct_0(X9964)))
        | ~ l1_orders_2(X9964) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_waybel_0])])])])])).

fof(c_0_64,plain,(
    ! [X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568,X1569,X1570,X1571,X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580] :
      ( ( ~ r2_hidden(X1570,X1569)
        | X1570 = X1561
        | X1570 = X1562
        | X1570 = X1563
        | X1570 = X1564
        | X1570 = X1565
        | X1570 = X1566
        | X1570 = X1567
        | X1570 = X1568
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1561
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1562
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1563
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1564
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1565
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1566
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1567
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( X1571 != X1568
        | r2_hidden(X1571,X1569)
        | X1569 != k6_enumset1(X1561,X1562,X1563,X1564,X1565,X1566,X1567,X1568) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1572
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1573
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1574
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1575
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1576
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1577
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1578
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) != X1579
        | ~ r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) )
      & ( r2_hidden(esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580),X1580)
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1572
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1573
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1574
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1575
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1576
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1577
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1578
        | esk64_9(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579,X1580) = X1579
        | X1580 = k6_enumset1(X1572,X1573,X1574,X1575,X1576,X1577,X1578,X1579) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_enumset1])])])])])])).

cnf(c_0_65,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r2_lattice3(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1155_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_33]),c_0_50])])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1154_0))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(esk1136_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X4,X5,X6,X7,X8,X9,X10) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1137_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43])).

fof(c_0_73,plain,(
    ! [X9972,X9973,X9974,X9975,X9979] :
      ( ( m1_subset_1(esk1138_4(X9972,X9973,X9974,X9975),u1_struct_0(X9972))
        | ~ r2_hidden(X9974,X9973)
        | ~ r2_hidden(X9975,X9973)
        | ~ m1_subset_1(X9975,u1_struct_0(X9972))
        | ~ m1_subset_1(X9974,u1_struct_0(X9972))
        | ~ v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( r2_hidden(esk1138_4(X9972,X9973,X9974,X9975),X9973)
        | ~ r2_hidden(X9974,X9973)
        | ~ r2_hidden(X9975,X9973)
        | ~ m1_subset_1(X9975,u1_struct_0(X9972))
        | ~ m1_subset_1(X9974,u1_struct_0(X9972))
        | ~ v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( r1_orders_2(X9972,esk1138_4(X9972,X9973,X9974,X9975),X9974)
        | ~ r2_hidden(X9974,X9973)
        | ~ r2_hidden(X9975,X9973)
        | ~ m1_subset_1(X9975,u1_struct_0(X9972))
        | ~ m1_subset_1(X9974,u1_struct_0(X9972))
        | ~ v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( r1_orders_2(X9972,esk1138_4(X9972,X9973,X9974,X9975),X9975)
        | ~ r2_hidden(X9974,X9973)
        | ~ r2_hidden(X9975,X9973)
        | ~ m1_subset_1(X9975,u1_struct_0(X9972))
        | ~ m1_subset_1(X9974,u1_struct_0(X9972))
        | ~ v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( m1_subset_1(esk1139_2(X9972,X9973),u1_struct_0(X9972))
        | v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( m1_subset_1(esk1140_2(X9972,X9973),u1_struct_0(X9972))
        | v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( r2_hidden(esk1139_2(X9972,X9973),X9973)
        | v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( r2_hidden(esk1140_2(X9972,X9973),X9973)
        | v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) )
      & ( ~ m1_subset_1(X9979,u1_struct_0(X9972))
        | ~ r2_hidden(X9979,X9973)
        | ~ r1_orders_2(X9972,X9979,esk1139_2(X9972,X9973))
        | ~ r1_orders_2(X9972,X9979,esk1140_2(X9972,X9973))
        | v2_waybel_0(X9973,X9972)
        | ~ m1_subset_1(X9973,k1_zfmisc_1(u1_struct_0(X9972)))
        | ~ l1_orders_2(X9972) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_waybel_0])])])])])).

cnf(c_0_74,plain,
    ( v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,esk1136_2(X2,X3),X1)
    | ~ r1_orders_2(X2,esk1137_2(X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk1154_0,X1,esk1155_0)
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_33]),c_0_50])]),c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( v1_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
    | r2_hidden(esk1136_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)),k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_62]),c_0_33])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).

cnf(c_0_78,negated_conjecture,
    ( v1_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
    | r2_hidden(esk1137_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)),k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_62]),c_0_33])])).

cnf(c_0_79,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( r2_hidden(esk1139_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( v1_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,esk1136_2(X2,X1),X3)
    | ~ r1_orders_2(X2,esk1137_2(X2,X1),X3)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_74,c_0_61])).

cnf(c_0_82,negated_conjecture,
    ( v1_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
    | r1_orders_2(esk1154_0,esk1136_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)),esk1155_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk1155_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_60])).

cnf(c_0_84,negated_conjecture,
    ( v1_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
    | r1_orders_2(esk1154_0,esk1137_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)),esk1155_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_78])).

cnf(c_0_85,plain,
    ( r2_hidden(esk1140_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_86,negated_conjecture,
    ( X1 = esk1155_0
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_60])).

cnf(c_0_87,negated_conjecture,
    ( v2_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
    | r2_hidden(esk1139_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)),k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_62]),c_0_33])])).

cnf(c_0_88,negated_conjecture,
    ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
    | ~ v2_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_89,negated_conjecture,
    ( v1_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_33]),c_0_62]),c_0_83])]),c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( v2_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0)
    | r2_hidden(esk1140_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)),k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_62]),c_0_33])])).

cnf(c_0_91,plain,
    ( v2_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,X1,esk1139_2(X2,X3))
    | ~ r1_orders_2(X2,X1,esk1140_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_92,negated_conjecture,
    ( esk1139_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) = esk1155_0
    | v2_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( ~ v2_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89])])).

cnf(c_0_94,negated_conjecture,
    ( esk1140_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) = esk1155_0
    | v2_waybel_0(k6_domain_1(u1_struct_0(esk1154_0),esk1155_0),esk1154_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_90])).

cnf(c_0_95,plain,
    ( v2_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,X3,esk1139_2(X2,X1))
    | ~ r1_orders_2(X2,X3,esk1140_2(X2,X1))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_91,c_0_61])).

cnf(c_0_96,negated_conjecture,
    ( esk1139_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) = esk1155_0 ),
    inference(sr,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( esk1140_2(esk1154_0,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) = esk1155_0 ),
    inference(sr,[status(thm)],[c_0_94,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk1154_0),esk1155_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97]),c_0_33]),c_0_62])]),c_0_93]),c_0_75])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_83,c_0_98]),
    [proof]).
%------------------------------------------------------------------------------
