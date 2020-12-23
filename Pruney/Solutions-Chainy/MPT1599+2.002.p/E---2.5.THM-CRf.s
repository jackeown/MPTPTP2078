%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 (6453 expanded)
%              Number of clauses        :   71 (2930 expanded)
%              Number of leaves         :   17 (1697 expanded)
%              Depth                    :   16
%              Number of atoms          :  351 (14733 expanded)
%              Number of equality atoms :   51 (4391 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(t7_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v2_lattice3(k2_yellow_1(X1))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(t25_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k12_lattice3(X1,X2,X3)
              <=> r3_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

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

fof(t16_lattice3,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( v4_orders_2(X1)
                   => k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).

fof(t15_lattice3,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(c_0_17,plain,(
    ! [X12,X13,X14,X15] :
      ( ( X12 = X14
        | g1_orders_2(X12,X13) != g1_orders_2(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) )
      & ( X13 = X15
        | g1_orders_2(X12,X13) != g1_orders_2(X14,X15)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_18,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_19,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | ~ v1_orders_2(X10)
      | X10 = g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_22,plain,(
    ! [X36] :
      ( v1_orders_2(k2_yellow_1(X36))
      & l1_orders_2(k2_yellow_1(X36)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_23,plain,(
    ! [X35] : k2_yellow_1(X35) = g1_orders_2(X35,k1_yellow_1(X35)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( v2_lattice3(k2_yellow_1(X1))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t7_yellow_1])).

cnf(c_0_25,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X37] :
      ( v1_orders_2(k2_yellow_1(X37))
      & v3_orders_2(k2_yellow_1(X37))
      & v4_orders_2(k2_yellow_1(X37))
      & v5_orders_2(k2_yellow_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & v2_lattice3(k2_yellow_1(esk1_0))
    & m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))
    & ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

fof(c_0_32,plain,(
    ! [X16,X17,X18] :
      ( v2_struct_0(X16)
      | ~ v3_orders_2(X16)
      | ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | r3_orders_2(X16,X17,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_33,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ v1_orders_2(g1_orders_2(X1,X2))
    | ~ l1_orders_2(g1_orders_2(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_34,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_36,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_40,plain,
    ( v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X38] :
      ( ( ~ v2_struct_0(k2_yellow_1(X38))
        | v1_xboole_0(X38) )
      & ( v1_orders_2(k2_yellow_1(X38))
        | v1_xboole_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_44,plain,
    ( r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X2)
    | v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_35])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))) ),
    inference(rw,[status(thm)],[c_0_42,c_0_28])).

fof(c_0_47,plain,(
    ! [X22,X23,X24] :
      ( ~ v5_orders_2(X22)
      | ~ v2_lattice3(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | k12_lattice3(X22,X23,X24) = k11_lattice3(X22,X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

fof(c_0_48,plain,(
    ! [X32,X33,X34] :
      ( ( X33 != k12_lattice3(X32,X33,X34)
        | r3_orders_2(X32,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v3_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ v2_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ r3_orders_2(X32,X33,X34)
        | X33 = k12_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ v3_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ v2_lattice3(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X1)
    | v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_39])).

fof(c_0_52,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r3_orders_2(k2_yellow_1(X39),X40,X41)
        | r1_tarski(X40,X41)
        | ~ m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))
        | ~ m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))
        | v1_xboole_0(X39) )
      & ( ~ r1_tarski(X40,X41)
        | r3_orders_2(k2_yellow_1(X39),X40,X41)
        | ~ m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))
        | ~ m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))
        | v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

cnf(c_0_53,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( X2 = k12_lattice3(X1,X2,X3)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)
    | v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( v2_lattice3(k2_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_59,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)
    | v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_62,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ v5_orders_2(X28)
      | ~ v2_lattice3(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,u1_struct_0(X28))
      | ~ m1_subset_1(X30,u1_struct_0(X28))
      | ~ m1_subset_1(X31,u1_struct_0(X28))
      | ~ v4_orders_2(X28)
      | k11_lattice3(X28,k11_lattice3(X28,X29,X30),X31) = k11_lattice3(X28,X29,k11_lattice3(X28,X30,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).

cnf(c_0_63,plain,
    ( k11_lattice3(X1,X2,X3) = X2
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( v2_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_28])).

cnf(c_0_66,plain,
    ( v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_28])).

cnf(c_0_67,plain,
    ( v4_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_68,plain,(
    ! [X25,X26,X27] :
      ( ~ v5_orders_2(X25)
      | ~ v2_lattice3(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | ~ m1_subset_1(X27,u1_struct_0(X25))
      | k11_lattice3(X25,X26,X27) = k11_lattice3(X25,X27,X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).

fof(c_0_69,plain,(
    ! [X19,X20,X21] :
      ( ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | ~ m1_subset_1(X21,u1_struct_0(X19))
      | m1_subset_1(k11_lattice3(X19,X20,X21),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

cnf(c_0_70,negated_conjecture,
    ( r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_60]),c_0_57])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_72,plain,
    ( r3_orders_2(X2,X1,X3)
    | X1 != k12_lattice3(X2,X1,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_73,plain,
    ( k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4) = k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v4_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_40]),c_0_39]),c_0_45]),c_0_35])])).

cnf(c_0_75,plain,
    ( v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_28])).

cnf(c_0_76,plain,
    ( k11_lattice3(X1,X2,X3) = k11_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_70]),c_0_65]),c_0_66]),c_0_40]),c_0_39]),c_0_51]),c_0_35])])).

fof(c_0_79,plain,(
    ! [X8,X9] : k1_setfam_1(k2_tarski(X8,X9)) = k3_xboole_0(X8,X9) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_80,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X5,X7)
      | r1_tarski(X5,k3_xboole_0(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_81,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_39]),c_0_39])).

cnf(c_0_82,plain,
    ( r3_orders_2(X1,X2,X3)
    | k11_lattice3(X1,X2,X3) != X2
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_53])).

cnf(c_0_83,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_65]),c_0_66]),c_0_39]),c_0_39]),c_0_45]),c_0_35])])).

cnf(c_0_84,plain,
    ( k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)) = k11_lattice3(X1,X4,k11_lattice3(X1,X2,X3))
    | ~ v4_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_73]),c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_78]),c_0_75]),c_0_65]),c_0_66]),c_0_39]),c_0_39]),c_0_51]),c_0_35])])).

cnf(c_0_86,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)),u1_struct_0(X1))
    | ~ v4_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_73]),c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_88,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_90,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3) != X2
    | ~ v2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_66]),c_0_40]),c_0_39]),c_0_39]),c_0_35])])).

cnf(c_0_91,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_74]),c_0_75]),c_0_65]),c_0_66]),c_0_39]),c_0_39]),c_0_45]),c_0_35])])).

cnf(c_0_92,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_84]),c_0_78]),c_0_75]),c_0_65]),c_0_66]),c_0_39]),c_0_39]),c_0_51]),c_0_35])])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0),esk1_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_78]),c_0_39]),c_0_75]),c_0_65]),c_0_66]),c_0_39]),c_0_51]),c_0_39]),c_0_35])])).

cnf(c_0_94,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_28]),c_0_88])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1) != X1
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_65]),c_0_45])]),c_0_57])).

cnf(c_0_97,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_92]),c_0_51]),c_0_45])])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_91]),c_0_45]),c_0_51])])).

cnf(c_0_99,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_76]),c_0_65]),c_0_66]),c_0_39]),c_0_39]),c_0_51]),c_0_35])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0)
    | ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1) != X1
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_92]),c_0_65]),c_0_51])]),c_0_57])).

cnf(c_0_103,negated_conjecture,
    ( k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)) = k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_91]),c_0_45]),c_0_51])])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])])).

cnf(c_0_105,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_98])]),c_0_104]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.20/0.42  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.20/0.42  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 0.20/0.42  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 0.20/0.42  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_yellow_1)).
% 0.20/0.42  fof(t7_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 0.20/0.42  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 0.20/0.42  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.20/0.42  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 0.20/0.42  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.20/0.42  fof(t25_yellow_0, axiom, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k12_lattice3(X1,X2,X3)<=>r3_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 0.20/0.42  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 0.20/0.42  fof(t16_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(v4_orders_2(X1)=>k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_lattice3)).
% 0.20/0.42  fof(t15_lattice3, axiom, ![X1]:(((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 0.20/0.42  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 0.20/0.42  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.42  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.20/0.42  fof(c_0_17, plain, ![X12, X13, X14, X15]:((X12=X14|g1_orders_2(X12,X13)!=g1_orders_2(X14,X15)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))))&(X13=X15|g1_orders_2(X12,X13)!=g1_orders_2(X14,X15)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.20/0.42  fof(c_0_18, plain, ![X11]:(~l1_orders_2(X11)|m1_subset_1(u1_orders_2(X11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X11))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.20/0.42  cnf(c_0_19, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  cnf(c_0_20, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.42  fof(c_0_21, plain, ![X10]:(~l1_orders_2(X10)|(~v1_orders_2(X10)|X10=g1_orders_2(u1_struct_0(X10),u1_orders_2(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 0.20/0.42  fof(c_0_22, plain, ![X36]:(v1_orders_2(k2_yellow_1(X36))&l1_orders_2(k2_yellow_1(X36))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 0.20/0.42  fof(c_0_23, plain, ![X35]:k2_yellow_1(X35)=g1_orders_2(X35,k1_yellow_1(X35)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 0.20/0.42  fof(c_0_24, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(v2_lattice3(k2_yellow_1(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>r1_tarski(k11_lattice3(k2_yellow_1(X1),X2,X3),k3_xboole_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t7_yellow_1])).
% 0.20/0.42  cnf(c_0_25, plain, (u1_struct_0(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X2,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.42  cnf(c_0_26, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.42  cnf(c_0_27, plain, (v1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_28, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_29, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  fof(c_0_30, plain, ![X37]:(((v1_orders_2(k2_yellow_1(X37))&v3_orders_2(k2_yellow_1(X37)))&v4_orders_2(k2_yellow_1(X37)))&v5_orders_2(k2_yellow_1(X37))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 0.20/0.42  fof(c_0_31, negated_conjecture, (~v1_xboole_0(esk1_0)&(v2_lattice3(k2_yellow_1(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))&(m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))&~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.20/0.42  fof(c_0_32, plain, ![X16, X17, X18]:(v2_struct_0(X16)|~v3_orders_2(X16)|~l1_orders_2(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|r3_orders_2(X16,X17,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.20/0.42  cnf(c_0_33, plain, (u1_struct_0(g1_orders_2(X1,X2))=X1|~v1_orders_2(g1_orders_2(X1,X2))|~l1_orders_2(g1_orders_2(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26])])).
% 0.20/0.42  cnf(c_0_34, plain, (v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.42  cnf(c_0_35, plain, (l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 0.20/0.42  cnf(c_0_36, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_38, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.42  cnf(c_0_39, plain, (u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.20/0.42  cnf(c_0_40, plain, (v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_36, c_0_28])).
% 0.20/0.42  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(rw,[status(thm)],[c_0_37, c_0_28])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(k2_yellow_1(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  fof(c_0_43, plain, ![X38]:((~v2_struct_0(k2_yellow_1(X38))|v1_xboole_0(X38))&(v1_orders_2(k2_yellow_1(X38))|v1_xboole_0(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 0.20/0.42  cnf(c_0_44, plain, (r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X2)|v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_35])])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk3_0,esk1_0)), inference(rw,[status(thm)],[c_0_41, c_0_39])).
% 0.20/0.42  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0))))), inference(rw,[status(thm)],[c_0_42, c_0_28])).
% 0.20/0.42  fof(c_0_47, plain, ![X22, X23, X24]:(~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)|~m1_subset_1(X23,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|k12_lattice3(X22,X23,X24)=k11_lattice3(X22,X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.20/0.42  fof(c_0_48, plain, ![X32, X33, X34]:((X33!=k12_lattice3(X32,X33,X34)|r3_orders_2(X32,X33,X34)|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(~v3_orders_2(X32)|~v5_orders_2(X32)|~v2_lattice3(X32)|~l1_orders_2(X32)))&(~r3_orders_2(X32,X33,X34)|X33=k12_lattice3(X32,X33,X34)|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(~v3_orders_2(X32)|~v5_orders_2(X32)|~v2_lattice3(X32)|~l1_orders_2(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_yellow_0])])])])).
% 0.20/0.42  cnf(c_0_49, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.42  cnf(c_0_50, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,X1)|v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))|~m1_subset_1(X1,esk1_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk2_0,esk1_0)), inference(rw,[status(thm)],[c_0_46, c_0_39])).
% 0.20/0.42  fof(c_0_52, plain, ![X39, X40, X41]:((~r3_orders_2(k2_yellow_1(X39),X40,X41)|r1_tarski(X40,X41)|~m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))|~m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))|v1_xboole_0(X39))&(~r1_tarski(X40,X41)|r3_orders_2(k2_yellow_1(X39),X40,X41)|~m1_subset_1(X41,u1_struct_0(k2_yellow_1(X39)))|~m1_subset_1(X40,u1_struct_0(k2_yellow_1(X39)))|v1_xboole_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 0.20/0.42  cnf(c_0_53, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.42  cnf(c_0_54, plain, (X2=k12_lattice3(X1,X2,X3)|~r3_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_55, plain, (v1_xboole_0(X1)|~v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_49, c_0_28])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)|v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))), inference(spm,[status(thm)],[c_0_50, c_0_45])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (v2_lattice3(k2_yellow_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_59, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_60, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)|v2_struct_0(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.42  cnf(c_0_61, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.42  fof(c_0_62, plain, ![X28, X29, X30, X31]:(~v5_orders_2(X28)|~v2_lattice3(X28)|~l1_orders_2(X28)|(~m1_subset_1(X29,u1_struct_0(X28))|(~m1_subset_1(X30,u1_struct_0(X28))|(~m1_subset_1(X31,u1_struct_0(X28))|(~v4_orders_2(X28)|k11_lattice3(X28,k11_lattice3(X28,X29,X30),X31)=k11_lattice3(X28,X29,k11_lattice3(X28,X30,X31))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_lattice3])])])).
% 0.20/0.42  cnf(c_0_63, plain, (k11_lattice3(X1,X2,X3)=X2|~v2_lattice3(X1)|~v5_orders_2(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.20/0.42  cnf(c_0_65, negated_conjecture, (v2_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)))), inference(rw,[status(thm)],[c_0_58, c_0_28])).
% 0.20/0.42  cnf(c_0_66, plain, (v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_59, c_0_28])).
% 0.20/0.42  cnf(c_0_67, plain, (v4_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  fof(c_0_68, plain, ![X25, X26, X27]:(~v5_orders_2(X25)|~v2_lattice3(X25)|~l1_orders_2(X25)|(~m1_subset_1(X26,u1_struct_0(X25))|(~m1_subset_1(X27,u1_struct_0(X25))|k11_lattice3(X25,X26,X27)=k11_lattice3(X25,X27,X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_lattice3])])])).
% 0.20/0.42  fof(c_0_69, plain, ![X19, X20, X21]:(~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))|m1_subset_1(k11_lattice3(X19,X20,X21),u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (r3_orders_2(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_60]), c_0_57])).
% 0.20/0.42  cnf(c_0_71, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_28]), c_0_28]), c_0_28])).
% 0.20/0.42  cnf(c_0_72, plain, (r3_orders_2(X2,X1,X3)|X1!=k12_lattice3(X2,X1,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X1,u1_struct_0(X2))|~v3_orders_2(X2)|~v5_orders_2(X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_73, plain, (k11_lattice3(X1,k11_lattice3(X1,X2,X3),X4)=k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~v4_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66]), c_0_40]), c_0_39]), c_0_45]), c_0_35])])).
% 0.20/0.42  cnf(c_0_75, plain, (v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_67, c_0_28])).
% 0.20/0.42  cnf(c_0_76, plain, (k11_lattice3(X1,X2,X3)=k11_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.42  cnf(c_0_77, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_70]), c_0_65]), c_0_66]), c_0_40]), c_0_39]), c_0_51]), c_0_35])])).
% 0.20/0.42  fof(c_0_79, plain, ![X8, X9]:k1_setfam_1(k2_tarski(X8,X9))=k3_xboole_0(X8,X9), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.42  fof(c_0_80, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X5,X7)|r1_tarski(X5,k3_xboole_0(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.20/0.42  cnf(c_0_81, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_39]), c_0_39])).
% 0.20/0.42  cnf(c_0_82, plain, (r3_orders_2(X1,X2,X3)|k11_lattice3(X1,X2,X3)!=X2|~v2_lattice3(X1)|~v5_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_72, c_0_53])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_65]), c_0_66]), c_0_39]), c_0_39]), c_0_45]), c_0_35])])).
% 0.20/0.42  cnf(c_0_84, plain, (k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4))=k11_lattice3(X1,X4,k11_lattice3(X1,X2,X3))|~v4_orders_2(X1)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_73]), c_0_77])).
% 0.20/0.42  cnf(c_0_85, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_78]), c_0_75]), c_0_65]), c_0_66]), c_0_39]), c_0_39]), c_0_51]), c_0_35])])).
% 0.20/0.42  cnf(c_0_86, plain, (m1_subset_1(k11_lattice3(X1,X2,k11_lattice3(X1,X3,X4)),u1_struct_0(X1))|~v4_orders_2(X1)|~v2_lattice3(X1)|~v5_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_73]), c_0_77])).
% 0.20/0.42  cnf(c_0_87, negated_conjecture, (~r1_tarski(k11_lattice3(k2_yellow_1(esk1_0),esk2_0,esk3_0),k3_xboole_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_88, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.42  cnf(c_0_89, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.42  cnf(c_0_90, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)!=X2|~v2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_66]), c_0_40]), c_0_39]), c_0_39]), c_0_35])])).
% 0.20/0.42  cnf(c_0_91, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk3_0)=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_74]), c_0_75]), c_0_65]), c_0_66]), c_0_39]), c_0_39]), c_0_45]), c_0_35])])).
% 0.20/0.42  cnf(c_0_92, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_84]), c_0_78]), c_0_75]), c_0_65]), c_0_66]), c_0_39]), c_0_39]), c_0_51]), c_0_35])])).
% 0.20/0.42  cnf(c_0_93, negated_conjecture, (m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0),esk1_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_78]), c_0_39]), c_0_75]), c_0_65]), c_0_66]), c_0_39]), c_0_51]), c_0_39]), c_0_35])])).
% 0.20/0.42  cnf(c_0_94, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),k1_setfam_1(k2_tarski(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_28]), c_0_88])).
% 0.20/0.42  cnf(c_0_95, plain, (r1_tarski(X1,k1_setfam_1(k2_tarski(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_89, c_0_88])).
% 0.20/0.42  cnf(c_0_96, negated_conjecture, (r1_tarski(X1,esk3_0)|k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,X1)!=X1|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_65]), c_0_45])]), c_0_57])).
% 0.20/0.42  cnf(c_0_97, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk3_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_92]), c_0_51]), c_0_45])])).
% 0.20/0.42  cnf(c_0_98, negated_conjecture, (m1_subset_1(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_91]), c_0_45]), c_0_51])])).
% 0.20/0.42  cnf(c_0_99, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),X1,esk2_0)|~m1_subset_1(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_76]), c_0_65]), c_0_66]), c_0_39]), c_0_39]), c_0_51]), c_0_35])])).
% 0.20/0.42  cnf(c_0_100, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0)|~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.20/0.42  cnf(c_0_101, negated_conjecture, (r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_98])])).
% 0.20/0.42  cnf(c_0_102, negated_conjecture, (r1_tarski(X1,esk2_0)|k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,X1)!=X1|~m1_subset_1(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_92]), c_0_65]), c_0_51])]), c_0_57])).
% 0.20/0.42  cnf(c_0_103, negated_conjecture, (k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0))=k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_91]), c_0_45]), c_0_51])])).
% 0.20/0.42  cnf(c_0_104, negated_conjecture, (~r1_tarski(k11_lattice3(g1_orders_2(esk1_0,k1_yellow_1(esk1_0)),esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])])).
% 0.20/0.42  cnf(c_0_105, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_98])]), c_0_104]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 106
% 0.20/0.42  # Proof object clause steps            : 71
% 0.20/0.42  # Proof object formula steps           : 35
% 0.20/0.42  # Proof object conjectures             : 36
% 0.20/0.42  # Proof object clause conjectures      : 33
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 25
% 0.20/0.42  # Proof object initial formulas used   : 17
% 0.20/0.42  # Proof object generating inferences   : 30
% 0.20/0.42  # Proof object simplifying inferences  : 123
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 17
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 29
% 0.20/0.42  # Removed in clause preprocessing      : 2
% 0.20/0.42  # Initial clauses in saturation        : 27
% 0.20/0.42  # Processed clauses                    : 461
% 0.20/0.42  # ...of these trivial                  : 5
% 0.20/0.42  # ...subsumed                          : 288
% 0.20/0.42  # ...remaining for further processing  : 168
% 0.20/0.42  # Other redundant clauses eliminated   : 17
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 3
% 0.20/0.42  # Backward-rewritten                   : 13
% 0.20/0.42  # Generated clauses                    : 1596
% 0.20/0.42  # ...of the previous two non-trivial   : 1257
% 0.20/0.42  # Contextual simplify-reflections      : 6
% 0.20/0.42  # Paramodulations                      : 1570
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 26
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 127
% 0.20/0.42  #    Positive orientable unit clauses  : 22
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 7
% 0.20/0.42  #    Non-unit-clauses                  : 98
% 0.20/0.42  # Current number of unprocessed clauses: 830
% 0.20/0.42  # ...number of literals in the above   : 4491
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 43
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 2042
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 966
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 186
% 0.20/0.42  # Unit Clause-clause subsumption calls : 72
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 26
% 0.20/0.42  # BW rewrite match successes           : 8
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 63222
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.071 s
% 0.20/0.42  # System time              : 0.005 s
% 0.20/0.42  # Total time               : 0.076 s
% 0.20/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
