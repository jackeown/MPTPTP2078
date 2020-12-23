%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t39_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:41 EDT 2019

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 537 expanded)
%              Number of clauses        :   48 ( 176 expanded)
%              Number of leaves         :    9 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  378 (3315 expanded)
%              Number of equality atoms :   51 ( 671 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   50 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',t39_yellow_0)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',t31_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',redefinition_r3_orders_2)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',reflexivity_r3_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',t7_yellow_0)).

fof(t30_yellow_0,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',t30_yellow_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t39_yellow_0.p',redefinition_k6_domain_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
              & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_yellow_0])).

fof(c_0_10,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( ( r1_lattice3(X38,X40,X39)
        | X39 != k2_yellow_0(X38,X40)
        | ~ r2_yellow_0(X38,X40)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ r1_lattice3(X38,X40,X41)
        | r1_orders_2(X38,X41,X39)
        | X39 != k2_yellow_0(X38,X40)
        | ~ r2_yellow_0(X38,X40)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( X39 = k2_yellow_0(X38,X42)
        | m1_subset_1(esk7_3(X38,X39,X42),u1_struct_0(X38))
        | ~ r1_lattice3(X38,X42,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( r2_yellow_0(X38,X42)
        | m1_subset_1(esk7_3(X38,X39,X42),u1_struct_0(X38))
        | ~ r1_lattice3(X38,X42,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( X39 = k2_yellow_0(X38,X42)
        | r1_lattice3(X38,X42,esk7_3(X38,X39,X42))
        | ~ r1_lattice3(X38,X42,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( r2_yellow_0(X38,X42)
        | r1_lattice3(X38,X42,esk7_3(X38,X39,X42))
        | ~ r1_lattice3(X38,X42,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( X39 = k2_yellow_0(X38,X42)
        | ~ r1_orders_2(X38,esk7_3(X38,X39,X42),X39)
        | ~ r1_lattice3(X38,X42,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) )
      & ( r2_yellow_0(X38,X42)
        | ~ r1_orders_2(X38,esk7_3(X38,X39,X42),X39)
        | ~ r1_lattice3(X38,X42,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | ~ v5_orders_2(X38)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( k1_yellow_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0
      | k2_yellow_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r3_orders_2(X22,X23,X24)
        | r1_orders_2(X22,X23,X24)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22)) )
      & ( ~ r1_orders_2(X22,X23,X24)
        | r3_orders_2(X22,X23,X24)
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ l1_orders_2(X22)
        | ~ m1_subset_1(X23,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(X22)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_13,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v3_orders_2(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | r3_orders_2(X25,X26,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_14,plain,(
    ! [X60] :
      ( v2_struct_0(X60)
      | ~ l1_struct_0(X60)
      | ~ v1_xboole_0(u1_struct_0(X60)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_15,plain,(
    ! [X15] :
      ( ~ l1_orders_2(X15)
      | l1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_16,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | r1_lattice3(X2,X3,esk7_3(X2,X1,X3))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X55,X56,X57] :
      ( ( ~ r1_lattice3(X55,k1_tarski(X57),X56)
        | r1_orders_2(X55,X56,X57)
        | ~ m1_subset_1(X57,u1_struct_0(X55))
        | ~ m1_subset_1(X56,u1_struct_0(X55))
        | ~ l1_orders_2(X55) )
      & ( ~ r1_orders_2(X55,X56,X57)
        | r1_lattice3(X55,k1_tarski(X57),X56)
        | ~ m1_subset_1(X57,u1_struct_0(X55))
        | ~ m1_subset_1(X56,u1_struct_0(X55))
        | ~ l1_orders_2(X55) )
      & ( ~ r2_lattice3(X55,k1_tarski(X57),X56)
        | r1_orders_2(X55,X57,X56)
        | ~ m1_subset_1(X57,u1_struct_0(X55))
        | ~ m1_subset_1(X56,u1_struct_0(X55))
        | ~ l1_orders_2(X55) )
      & ( ~ r1_orders_2(X55,X57,X56)
        | r2_lattice3(X55,k1_tarski(X57),X56)
        | ~ m1_subset_1(X57,u1_struct_0(X55))
        | ~ m1_subset_1(X56,u1_struct_0(X55))
        | ~ l1_orders_2(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_yellow_0])])])])).

cnf(c_0_21,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | m1_subset_1(esk7_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( ( r2_lattice3(X32,X34,X33)
        | X33 != k1_yellow_0(X32,X34)
        | ~ r1_yellow_0(X32,X34)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r2_lattice3(X32,X34,X35)
        | r1_orders_2(X32,X33,X35)
        | X33 != k1_yellow_0(X32,X34)
        | ~ r1_yellow_0(X32,X34)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( X33 = k1_yellow_0(X32,X36)
        | m1_subset_1(esk6_3(X32,X33,X36),u1_struct_0(X32))
        | ~ r2_lattice3(X32,X36,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( r1_yellow_0(X32,X36)
        | m1_subset_1(esk6_3(X32,X33,X36),u1_struct_0(X32))
        | ~ r2_lattice3(X32,X36,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( X33 = k1_yellow_0(X32,X36)
        | r2_lattice3(X32,X36,esk6_3(X32,X33,X36))
        | ~ r2_lattice3(X32,X36,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( r1_yellow_0(X32,X36)
        | r2_lattice3(X32,X36,esk6_3(X32,X33,X36))
        | ~ r2_lattice3(X32,X36,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( X33 = k1_yellow_0(X32,X36)
        | ~ r1_orders_2(X32,X33,esk6_3(X32,X33,X36))
        | ~ r2_lattice3(X32,X36,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( r1_yellow_0(X32,X36)
        | ~ r1_orders_2(X32,X33,esk6_3(X32,X33,X36))
        | ~ r2_lattice3(X32,X36,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( k2_yellow_0(esk1_0,X1) = esk2_0
    | r1_lattice3(esk1_0,X1,esk7_3(esk1_0,esk2_0,X1))
    | ~ r1_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,k1_tarski(X3),X2)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r3_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_22])]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_18]),c_0_22])]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( k2_yellow_0(esk1_0,X1) = esk2_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r1_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_34,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | r2_lattice3(X2,X3,esk6_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | m1_subset_1(esk6_3(X2,X1,X3),u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_36,plain,(
    ! [X20,X21] :
      ( v1_xboole_0(X20)
      | ~ m1_subset_1(X21,X20)
      | k6_domain_1(X20,X21) = k1_tarski(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k2_yellow_0(esk1_0,k1_tarski(X1)) = esk2_0
    | r1_lattice3(esk1_0,k1_tarski(X1),esk7_3(esk1_0,esk2_0,k1_tarski(X1)))
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17]),c_0_18])])).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_17])])).

cnf(c_0_40,negated_conjecture,
    ( k2_yellow_0(esk1_0,k1_tarski(X1)) = esk2_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,k1_tarski(X1)),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_17]),c_0_18])])).

cnf(c_0_41,negated_conjecture,
    ( k1_yellow_0(esk1_0,X1) = esk2_0
    | r2_lattice3(esk1_0,X1,esk6_3(esk1_0,esk2_0,X1))
    | ~ r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_42,plain,
    ( r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( k1_yellow_0(esk1_0,X1) = esk2_0
    | m1_subset_1(esk6_3(esk1_0,esk2_0,X1),u1_struct_0(esk1_0))
    | ~ r2_lattice3(esk1_0,X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_37]),c_0_18])])).

cnf(c_0_46,plain,
    ( r1_orders_2(X1,X3,X2)
    | ~ r1_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( k2_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r1_lattice3(esk1_0,k1_tarski(esk2_0),esk7_3(esk1_0,esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_17])])).

cnf(c_0_48,negated_conjecture,
    ( k2_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | m1_subset_1(esk7_3(esk1_0,esk2_0,k1_tarski(esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_17])])).

cnf(c_0_49,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(X1)) = esk2_0
    | r2_lattice3(esk1_0,k1_tarski(X1),esk6_3(esk1_0,esk2_0,k1_tarski(X1)))
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_17]),c_0_18])])).

cnf(c_0_50,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(X1)) = esk2_0
    | m1_subset_1(esk6_3(esk1_0,esk2_0,k1_tarski(X1)),u1_struct_0(esk1_0))
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_17]),c_0_18])])).

cnf(c_0_51,negated_conjecture,
    ( k1_yellow_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0
    | k2_yellow_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_45])).

cnf(c_0_53,plain,
    ( X1 = k2_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,esk7_3(X2,X1,X3),X1)
    | ~ r1_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( k2_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r1_orders_2(esk1_0,esk7_3(esk1_0,esk2_0,k1_tarski(esk2_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_17]),c_0_18])]),c_0_48])).

cnf(c_0_55,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r2_lattice3(X1,k1_tarski(X2),X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r2_lattice3(esk1_0,k1_tarski(esk2_0),esk6_3(esk1_0,esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_39]),c_0_17])])).

cnf(c_0_57,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | m1_subset_1(esk6_3(esk1_0,esk2_0,k1_tarski(esk2_0)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_17])])).

cnf(c_0_58,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(esk2_0)) != esk2_0
    | k2_yellow_0(esk1_0,k1_tarski(esk2_0)) != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | ~ r1_lattice3(esk1_0,k1_tarski(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_60,plain,
    ( X1 = k1_yellow_0(X2,X3)
    | ~ r1_orders_2(X2,X1,esk6_3(X2,X1,X3))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_61,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r1_orders_2(esk1_0,esk2_0,esk6_3(esk1_0,esk2_0,k1_tarski(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_17]),c_0_18])]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(esk2_0)) != esk2_0
    | ~ r1_lattice3(esk1_0,k1_tarski(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k1_yellow_0(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | ~ r2_lattice3(esk1_0,k1_tarski(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,k1_tarski(esk2_0),esk2_0)
    | ~ r2_lattice3(esk1_0,k1_tarski(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_lattice3(esk1_0,k1_tarski(esk2_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_39]),c_0_17]),c_0_18])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_30]),c_0_39]),c_0_17]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
