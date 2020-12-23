%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:46 EST 2020

% Result     : Theorem 23.12s
% Output     : CNFRefutation 23.12s
% Verified   : 
% Statistics : Number of formulae       :  119 (2322 expanded)
%              Number of clauses        :   76 (1007 expanded)
%              Number of leaves         :   20 ( 641 expanded)
%              Depth                    :   22
%              Number of atoms          :  555 (6032 expanded)
%              Number of equality atoms :   26 (1564 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow_1)).

fof(t9_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r2_hidden(k3_xboole_0(X2,X3),X1)
               => k11_lattice3(k2_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_1)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(t3_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
             => ( r3_orders_2(k2_yellow_1(X1),X2,X3)
              <=> r1_tarski(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(dt_k11_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(t12_yellow_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r2_hidden(X3,X1) )
           => r2_hidden(k3_xboole_0(X2,X3),X1) )
       => v2_lattice3(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_yellow_1)).

fof(fc5_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & v3_orders_2(k2_yellow_1(X1))
      & v4_orders_2(k2_yellow_1(X1))
      & v5_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(fc6_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( ~ v2_struct_0(k2_yellow_1(X1))
        & v1_orders_2(k2_yellow_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t16_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t21_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v2_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r2_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

fof(t8_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) ) )
                    & ( ( r1_orders_2(X1,X2,X3)
                        & r1_orders_2(X1,X2,X4) )
                     => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
                    & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
                     => ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) ) )
                    & ( ( r1_orders_2(X1,X3,X2)
                        & r1_orders_2(X1,X4,X2) )
                     => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(c_0_19,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X15 = X17
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) )
      & ( X16 = X18
        | g1_orders_2(X15,X16) != g1_orders_2(X17,X18)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_20,plain,(
    ! [X42] :
      ( v1_relat_2(k1_yellow_1(X42))
      & v4_relat_2(k1_yellow_1(X42))
      & v8_relat_2(k1_yellow_1(X42))
      & v1_partfun1(k1_yellow_1(X42),X42)
      & m1_subset_1(k1_yellow_1(X42),k1_zfmisc_1(k2_zfmisc_1(X42,X42))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

fof(c_0_21,plain,(
    ! [X43] :
      ( v1_orders_2(k2_yellow_1(X43))
      & l1_orders_2(k2_yellow_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_22,plain,(
    ! [X41] : k2_yellow_1(X41) = g1_orders_2(X41,k1_yellow_1(X41)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_23,plain,(
    ! [X49,X50,X51] :
      ( v1_xboole_0(X49)
      | ~ m1_subset_1(X50,u1_struct_0(k2_yellow_1(X49)))
      | ~ m1_subset_1(X51,u1_struct_0(k2_yellow_1(X49)))
      | ~ r2_hidden(k3_xboole_0(X50,X51),X49)
      | k11_lattice3(k2_yellow_1(X49),X50,X51) = k3_xboole_0(X50,X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_yellow_1])])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X14] :
      ( ~ l1_orders_2(X14)
      | ~ v1_orders_2(X14)
      | X14 = g1_orders_2(u1_struct_0(X14),u1_orders_2(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_27,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | k11_lattice3(k2_yellow_1(X1),X2,X3) = k3_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X1 = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_35,plain,(
    ! [X46,X47,X48] :
      ( ( ~ r3_orders_2(k2_yellow_1(X46),X47,X48)
        | r1_tarski(X47,X48)
        | ~ m1_subset_1(X48,u1_struct_0(k2_yellow_1(X46)))
        | ~ m1_subset_1(X47,u1_struct_0(k2_yellow_1(X46)))
        | v1_xboole_0(X46) )
      & ( ~ r1_tarski(X47,X48)
        | r3_orders_2(k2_yellow_1(X46),X47,X48)
        | ~ m1_subset_1(X48,u1_struct_0(k2_yellow_1(X46)))
        | ~ m1_subset_1(X47,u1_struct_0(k2_yellow_1(X46)))
        | v1_xboole_0(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).

fof(c_0_36,plain,(
    ! [X22,X23,X24] :
      ( ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | m1_subset_1(k11_lattice3(X22,X23,X24),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).

cnf(c_0_37,plain,
    ( k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3) = k3_xboole_0(X2,X3)
    | v1_xboole_0(X1)
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_38,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32])]),c_0_33]),c_0_34])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ( ! [X2,X3] :
              ( ( r2_hidden(X2,X1)
                & r2_hidden(X3,X1) )
             => r2_hidden(k3_xboole_0(X2,X3),X1) )
         => v2_lattice3(k2_yellow_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t12_yellow_1])).

cnf(c_0_40,plain,
    ( r3_orders_2(k2_yellow_1(X3),X1,X2)
    | v1_xboole_0(X3)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X44] :
      ( v1_orders_2(k2_yellow_1(X44))
      & v3_orders_2(k2_yellow_1(X44))
      & v4_orders_2(k2_yellow_1(X44))
      & v5_orders_2(k2_yellow_1(X44)) ) ),
    inference(variable_rename,[status(thm)],[fc5_yellow_1])).

fof(c_0_42,plain,(
    ! [X45] :
      ( ( ~ v2_struct_0(k2_yellow_1(X45))
        | v1_xboole_0(X45) )
      & ( v1_orders_2(k2_yellow_1(X45))
        | v1_xboole_0(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3) = k3_xboole_0(X2,X3)
    | v1_xboole_0(X1)
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38])).

fof(c_0_45,negated_conjecture,(
    ! [X53,X54] :
      ( ~ v1_xboole_0(esk5_0)
      & ( ~ r2_hidden(X53,esk5_0)
        | ~ r2_hidden(X54,esk5_0)
        | r2_hidden(k3_xboole_0(X53,X54),esk5_0) )
      & ~ v2_lattice3(k2_yellow_1(esk5_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_39])])])])])).

fof(c_0_46,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r3_orders_2(X19,X20,X21)
        | r1_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) )
      & ( ~ r1_orders_2(X19,X20,X21)
        | r3_orders_2(X19,X20,X21)
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X3)
    | r3_orders_2(g1_orders_2(X3,k1_yellow_1(X3)),X1,X2)
    | ~ r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))))
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_48,plain,
    ( v3_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_xboole_0(X2,X3),X1)
    | ~ r2_hidden(k3_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38]),c_0_34]),c_0_38]),c_0_38])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k3_xboole_0(X1,X2),esk5_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,X13)
      | v1_xboole_0(X13)
      | r2_hidden(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_54,plain,(
    ! [X25,X26,X28,X29,X30] :
      ( ( m1_subset_1(esk1_2(X25,X26),u1_struct_0(X25))
        | ~ r2_yellow_0(X25,X26)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_lattice3(X25,X26,esk1_2(X25,X26))
        | ~ r2_yellow_0(X25,X26)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ r1_lattice3(X25,X26,X28)
        | r1_orders_2(X25,X28,esk1_2(X25,X26))
        | ~ r2_yellow_0(X25,X26)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk2_3(X25,X29,X30),u1_struct_0(X25))
        | ~ m1_subset_1(X30,u1_struct_0(X25))
        | ~ r1_lattice3(X25,X29,X30)
        | r2_yellow_0(X25,X29)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( r1_lattice3(X25,X29,esk2_3(X25,X29,X30))
        | ~ m1_subset_1(X30,u1_struct_0(X25))
        | ~ r1_lattice3(X25,X29,X30)
        | r2_yellow_0(X25,X29)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ r1_orders_2(X25,esk2_3(X25,X29,X30),X30)
        | ~ m1_subset_1(X30,u1_struct_0(X25))
        | ~ r1_lattice3(X25,X29,X30)
        | r2_yellow_0(X25,X29)
        | ~ v5_orders_2(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).

cnf(c_0_55,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_38]),c_0_38])).

cnf(c_0_57,plain,
    ( v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_48,c_0_28])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_59,plain,
    ( v5_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,X2),esk5_0)
    | ~ r2_hidden(X2,esk5_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_62,plain,(
    ! [X1,X4,X3,X2] :
      ( epred1_4(X2,X3,X4,X1)
    <=> ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) ) )
        & ( ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) )
         => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
        & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) ) )
        & ( ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) )
         => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ),
    introduced(definition)).

cnf(c_0_63,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1)
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_34]),c_0_38]),c_0_38])]),c_0_58])).

cnf(c_0_65,plain,
    ( v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,X2),esk5_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_52])).

fof(c_0_67,plain,(
    ! [X1,X4,X3,X2] :
      ( epred1_4(X2,X3,X4,X1)
     => ( ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) ) )
        & ( ( r1_orders_2(X1,X2,X3)
            & r1_orders_2(X1,X2,X4) )
         => r1_lattice3(X1,k2_tarski(X3,X4),X2) )
        & ( r2_lattice3(X1,k2_tarski(X3,X4),X2)
         => ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) ) )
        & ( ( r1_orders_2(X1,X3,X2)
            & r1_orders_2(X1,X4,X2) )
         => r2_lattice3(X1,k2_tarski(X3,X4),X2) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),X2)
    | v1_xboole_0(X1)
    | ~ r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3),X1)
    | ~ m1_subset_1(X3,X1)
    | ~ r1_tarski(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3),X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_34]),c_0_38])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k3_xboole_0(X1,X2),esk5_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_61]),c_0_52])).

fof(c_0_70,plain,(
    ! [X9,X10,X11] :
      ( ~ r1_tarski(X9,X10)
      | ~ r1_tarski(X9,X11)
      | r1_tarski(X9,k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

fof(c_0_71,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v2_lattice3(X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | r2_yellow_0(X32,k2_tarski(X33,X34))
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk3_1(X32),u1_struct_0(X32))
        | v2_lattice3(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk4_1(X32),u1_struct_0(X32))
        | v2_lattice3(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ r2_yellow_0(X32,k2_tarski(esk3_1(X32),esk4_1(X32)))
        | v2_lattice3(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).

cnf(c_0_72,plain,
    ( r1_tarski(X2,X3)
    | v1_xboole_0(X1)
    | ~ r3_orders_2(k2_yellow_1(X1),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_73,plain,(
    ! [X55,X56,X57,X58] :
      ( ( r1_orders_2(X55,X58,X57)
        | ~ r1_lattice3(X55,k2_tarski(X57,X56),X58)
        | ~ epred1_4(X58,X57,X56,X55) )
      & ( r1_orders_2(X55,X58,X56)
        | ~ r1_lattice3(X55,k2_tarski(X57,X56),X58)
        | ~ epred1_4(X58,X57,X56,X55) )
      & ( ~ r1_orders_2(X55,X58,X57)
        | ~ r1_orders_2(X55,X58,X56)
        | r1_lattice3(X55,k2_tarski(X57,X56),X58)
        | ~ epred1_4(X58,X57,X56,X55) )
      & ( r1_orders_2(X55,X57,X58)
        | ~ r2_lattice3(X55,k2_tarski(X57,X56),X58)
        | ~ epred1_4(X58,X57,X56,X55) )
      & ( r1_orders_2(X55,X56,X58)
        | ~ r2_lattice3(X55,k2_tarski(X57,X56),X58)
        | ~ epred1_4(X58,X57,X56,X55) )
      & ( ~ r1_orders_2(X55,X57,X58)
        | ~ r1_orders_2(X55,X56,X58)
        | r2_lattice3(X55,k2_tarski(X57,X56),X58)
        | ~ epred1_4(X58,X57,X56,X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_67])])])).

fof(c_0_74,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => epred1_4(X2,X3,X4,X1) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t8_yellow_0,c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)
    | ~ r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3))
    | ~ m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),esk5_0)
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),k3_xboole_0(X2,X3)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_52])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(X1))
    | v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( ~ v2_lattice3(k2_yellow_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_79,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))
    | ~ m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_80,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_lattice3(X1,k2_tarski(X4,X3),X2)
    | ~ epred1_4(X2,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,plain,
    ( r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_82,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ l1_orders_2(X37)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | ~ m1_subset_1(X39,u1_struct_0(X37))
      | ~ m1_subset_1(X40,u1_struct_0(X37))
      | epred1_4(X38,X39,X40,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).

cnf(c_0_83,negated_conjecture,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)
    | ~ r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3))
    | ~ m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),esk5_0)
    | ~ m1_subset_1(X3,esk5_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),X3)
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,plain,
    ( v2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))
    | m1_subset_1(esk4_1(g1_orders_2(X1,k1_yellow_1(X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_38]),c_0_65]),c_0_34])])).

cnf(c_0_85,negated_conjecture,
    ( ~ v2_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_78,c_0_28])).

cnf(c_0_86,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_38]),c_0_38])).

cnf(c_0_88,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_89,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X3)
    | ~ epred1_4(esk2_3(X1,k2_tarski(X2,X3),X4),X2,X3,X1)
    | ~ r1_lattice3(X1,k2_tarski(X2,X3),X4)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_90,plain,
    ( epred1_4(X2,X3,X4,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_92,plain,
    ( r1_orders_2(X1,X2,X3)
    | ~ r1_lattice3(X1,k2_tarski(X3,X4),X2)
    | ~ epred1_4(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_93,negated_conjecture,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)
    | ~ r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk5_0)
    | ~ m1_subset_1(X2,esk5_0)
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_94,plain,
    ( v2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))
    | m1_subset_1(esk3_1(g1_orders_2(X1,k1_yellow_1(X1))),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_38]),c_0_65]),c_0_34])])).

cnf(c_0_95,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(X2,X3)
    | ~ r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_57]),c_0_34]),c_0_38]),c_0_38])]),c_0_58])).

cnf(c_0_96,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X3)
    | ~ r1_lattice3(X1,k2_tarski(X2,X3),X4)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_97,plain,
    ( r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),X2)
    | m1_subset_1(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3),X1)
    | ~ r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)
    | ~ m1_subset_1(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_38]),c_0_65]),c_0_34])])).

cnf(c_0_98,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X2)
    | ~ epred1_4(esk2_3(X1,k2_tarski(X2,X3),X4),X2,X3,X1)
    | ~ r1_lattice3(X1,k2_tarski(X2,X3),X4)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_81])).

cnf(c_0_99,negated_conjecture,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)
    | ~ r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk5_0)
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_85])).

cnf(c_0_100,plain,
    ( r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3))
    | v1_xboole_0(X1)
    | r1_tarski(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4),X3)
    | ~ r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_65]),c_0_34]),c_0_38]),c_0_38]),c_0_38])]),c_0_97])).

cnf(c_0_101,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X2)
    | ~ r1_lattice3(X1,k2_tarski(X2,X3),X4)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_90]),c_0_91])).

cnf(c_0_102,negated_conjecture,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(X1,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(X1,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ m1_subset_1(k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk5_0)
    | ~ m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)
    | ~ m1_subset_1(X1,esk5_0)
    | ~ r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(X1,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_52]),c_0_97])).

cnf(c_0_103,plain,
    ( r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3))
    | v1_xboole_0(X1)
    | r1_tarski(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4),X2)
    | ~ r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X4,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_101]),c_0_65]),c_0_34]),c_0_38]),c_0_38]),c_0_38])]),c_0_97])).

cnf(c_0_104,plain,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)
    | ~ m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_52]),c_0_69])).

cnf(c_0_105,plain,
    ( r1_lattice3(X1,k2_tarski(X3,X4),X2)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X2,X4)
    | ~ epred1_4(X2,X3,X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

fof(c_0_106,plain,(
    ! [X7,X8] : r1_tarski(k3_xboole_0(X7,X8),X7) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_107,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_108,plain,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ epred1_4(k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))
    | ~ r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))
    | ~ r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))
    | ~ m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)
    | ~ m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_110,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_111,plain,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))
    | ~ r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))
    | ~ m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)
    | ~ m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_90]),c_0_34]),c_0_38]),c_0_38]),c_0_38])]),c_0_69])).

cnf(c_0_112,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_113,plain,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))
    | ~ m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)
    | ~ m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_64]),c_0_112])]),c_0_52]),c_0_69])).

cnf(c_0_114,plain,
    ( v2_lattice3(X1)
    | ~ r2_yellow_0(X1,k2_tarski(esk3_1(X1),esk4_1(X1)))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_115,plain,
    ( r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))
    | ~ m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)
    | ~ m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_64]),c_0_109])]),c_0_52]),c_0_69])).

cnf(c_0_116,plain,
    ( ~ m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)
    | ~ m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_65]),c_0_34])]),c_0_85])).

cnf(c_0_117,plain,
    ( ~ m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_84]),c_0_85])).

cnf(c_0_118,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_94]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n008.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:56:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 23.12/23.31  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 23.12/23.31  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 23.12/23.31  #
% 23.12/23.31  # Preprocessing time       : 0.030 s
% 23.12/23.31  # Presaturation interreduction done
% 23.12/23.31  
% 23.12/23.31  # Proof found!
% 23.12/23.31  # SZS status Theorem
% 23.12/23.31  # SZS output start CNFRefutation
% 23.12/23.31  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 23.12/23.31  fof(dt_k1_yellow_1, axiom, ![X1]:((((v1_relat_2(k1_yellow_1(X1))&v4_relat_2(k1_yellow_1(X1)))&v8_relat_2(k1_yellow_1(X1)))&v1_partfun1(k1_yellow_1(X1),X1))&m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_1)).
% 23.12/23.31  fof(dt_k2_yellow_1, axiom, ![X1]:(v1_orders_2(k2_yellow_1(X1))&l1_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 23.12/23.31  fof(d1_yellow_1, axiom, ![X1]:k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow_1)).
% 23.12/23.31  fof(t9_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r2_hidden(k3_xboole_0(X2,X3),X1)=>k11_lattice3(k2_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_1)).
% 23.12/23.31  fof(abstractness_v1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v1_orders_2(X1)=>X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_orders_2)).
% 23.12/23.31  fof(t3_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))=>(r3_orders_2(k2_yellow_1(X1),X2,X3)<=>r1_tarski(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 23.12/23.31  fof(dt_k11_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 23.12/23.31  fof(t12_yellow_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>(![X2, X3]:((r2_hidden(X2,X1)&r2_hidden(X3,X1))=>r2_hidden(k3_xboole_0(X2,X3),X1))=>v2_lattice3(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_yellow_1)).
% 23.12/23.31  fof(fc5_yellow_1, axiom, ![X1]:(((v1_orders_2(k2_yellow_1(X1))&v3_orders_2(k2_yellow_1(X1)))&v4_orders_2(k2_yellow_1(X1)))&v5_orders_2(k2_yellow_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 23.12/23.31  fof(fc6_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(~(v2_struct_0(k2_yellow_1(X1)))&v1_orders_2(k2_yellow_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 23.12/23.31  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 23.12/23.31  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 23.12/23.31  fof(t16_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r2_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r1_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_yellow_0)).
% 23.12/23.31  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 23.12/23.31  fof(t21_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>(v2_lattice3(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r2_yellow_0(X1,k2_tarski(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow_0)).
% 23.12/23.31  fof(t8_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_yellow_0)).
% 23.12/23.31  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 23.12/23.31  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.12/23.31  fof(c_0_19, plain, ![X15, X16, X17, X18]:((X15=X17|g1_orders_2(X15,X16)!=g1_orders_2(X17,X18)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))))&(X16=X18|g1_orders_2(X15,X16)!=g1_orders_2(X17,X18)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X15,X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 23.12/23.31  fof(c_0_20, plain, ![X42]:((((v1_relat_2(k1_yellow_1(X42))&v4_relat_2(k1_yellow_1(X42)))&v8_relat_2(k1_yellow_1(X42)))&v1_partfun1(k1_yellow_1(X42),X42))&m1_subset_1(k1_yellow_1(X42),k1_zfmisc_1(k2_zfmisc_1(X42,X42)))), inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).
% 23.12/23.31  fof(c_0_21, plain, ![X43]:(v1_orders_2(k2_yellow_1(X43))&l1_orders_2(k2_yellow_1(X43))), inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).
% 23.12/23.31  fof(c_0_22, plain, ![X41]:k2_yellow_1(X41)=g1_orders_2(X41,k1_yellow_1(X41)), inference(variable_rename,[status(thm)],[d1_yellow_1])).
% 23.12/23.31  fof(c_0_23, plain, ![X49, X50, X51]:(v1_xboole_0(X49)|(~m1_subset_1(X50,u1_struct_0(k2_yellow_1(X49)))|(~m1_subset_1(X51,u1_struct_0(k2_yellow_1(X49)))|(~r2_hidden(k3_xboole_0(X50,X51),X49)|k11_lattice3(k2_yellow_1(X49),X50,X51)=k3_xboole_0(X50,X51))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_yellow_1])])])])).
% 23.12/23.31  cnf(c_0_24, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 23.12/23.31  cnf(c_0_25, plain, (m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 23.12/23.31  fof(c_0_26, plain, ![X14]:(~l1_orders_2(X14)|(~v1_orders_2(X14)|X14=g1_orders_2(u1_struct_0(X14),u1_orders_2(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).
% 23.12/23.31  cnf(c_0_27, plain, (v1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 23.12/23.31  cnf(c_0_28, plain, (k2_yellow_1(X1)=g1_orders_2(X1,k1_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 23.12/23.31  cnf(c_0_29, plain, (l1_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 23.12/23.31  cnf(c_0_30, plain, (v1_xboole_0(X1)|k11_lattice3(k2_yellow_1(X1),X2,X3)=k3_xboole_0(X2,X3)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~r2_hidden(k3_xboole_0(X2,X3),X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 23.12/23.31  cnf(c_0_31, plain, (X1=X2|g1_orders_2(X1,k1_yellow_1(X1))!=g1_orders_2(X2,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 23.12/23.31  cnf(c_0_32, plain, (X1=g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))|~l1_orders_2(X1)|~v1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 23.12/23.31  cnf(c_0_33, plain, (v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 23.12/23.31  cnf(c_0_34, plain, (l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_29, c_0_28])).
% 23.12/23.31  fof(c_0_35, plain, ![X46, X47, X48]:((~r3_orders_2(k2_yellow_1(X46),X47,X48)|r1_tarski(X47,X48)|~m1_subset_1(X48,u1_struct_0(k2_yellow_1(X46)))|~m1_subset_1(X47,u1_struct_0(k2_yellow_1(X46)))|v1_xboole_0(X46))&(~r1_tarski(X47,X48)|r3_orders_2(k2_yellow_1(X46),X47,X48)|~m1_subset_1(X48,u1_struct_0(k2_yellow_1(X46)))|~m1_subset_1(X47,u1_struct_0(k2_yellow_1(X46)))|v1_xboole_0(X46))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_yellow_1])])])])])).
% 23.12/23.31  fof(c_0_36, plain, ![X22, X23, X24]:(~l1_orders_2(X22)|~m1_subset_1(X23,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(X22))|m1_subset_1(k11_lattice3(X22,X23,X24),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k11_lattice3])])).
% 23.12/23.31  cnf(c_0_37, plain, (k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)=k3_xboole_0(X2,X3)|v1_xboole_0(X1)|~r2_hidden(k3_xboole_0(X2,X3),X1)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_28]), c_0_28]), c_0_28])).
% 23.12/23.31  cnf(c_0_38, plain, (u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32])]), c_0_33]), c_0_34])])).
% 23.12/23.31  fof(c_0_39, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>(![X2, X3]:((r2_hidden(X2,X1)&r2_hidden(X3,X1))=>r2_hidden(k3_xboole_0(X2,X3),X1))=>v2_lattice3(k2_yellow_1(X1))))), inference(assume_negation,[status(cth)],[t12_yellow_1])).
% 23.12/23.31  cnf(c_0_40, plain, (r3_orders_2(k2_yellow_1(X3),X1,X2)|v1_xboole_0(X3)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X3)))|~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 23.12/23.31  fof(c_0_41, plain, ![X44]:(((v1_orders_2(k2_yellow_1(X44))&v3_orders_2(k2_yellow_1(X44)))&v4_orders_2(k2_yellow_1(X44)))&v5_orders_2(k2_yellow_1(X44))), inference(variable_rename,[status(thm)],[fc5_yellow_1])).
% 23.12/23.31  fof(c_0_42, plain, ![X45]:((~v2_struct_0(k2_yellow_1(X45))|v1_xboole_0(X45))&(v1_orders_2(k2_yellow_1(X45))|v1_xboole_0(X45))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_yellow_1])])])])).
% 23.12/23.31  cnf(c_0_43, plain, (m1_subset_1(k11_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 23.12/23.31  cnf(c_0_44, plain, (k11_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)=k3_xboole_0(X2,X3)|v1_xboole_0(X1)|~r2_hidden(k3_xboole_0(X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38])).
% 23.12/23.31  fof(c_0_45, negated_conjecture, ![X53, X54]:(~v1_xboole_0(esk5_0)&((~r2_hidden(X53,esk5_0)|~r2_hidden(X54,esk5_0)|r2_hidden(k3_xboole_0(X53,X54),esk5_0))&~v2_lattice3(k2_yellow_1(esk5_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_39])])])])])).
% 23.12/23.31  fof(c_0_46, plain, ![X19, X20, X21]:((~r3_orders_2(X19,X20,X21)|r1_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))&(~r1_orders_2(X19,X20,X21)|r3_orders_2(X19,X20,X21)|(v2_struct_0(X19)|~v3_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,u1_struct_0(X19))|~m1_subset_1(X21,u1_struct_0(X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 23.12/23.31  cnf(c_0_47, plain, (v1_xboole_0(X3)|r3_orders_2(g1_orders_2(X3,k1_yellow_1(X3)),X1,X2)|~r1_tarski(X1,X2)|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))))|~m1_subset_1(X1,u1_struct_0(g1_orders_2(X3,k1_yellow_1(X3))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_28]), c_0_28]), c_0_28])).
% 23.12/23.31  cnf(c_0_48, plain, (v3_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 23.12/23.31  cnf(c_0_49, plain, (v1_xboole_0(X1)|~v2_struct_0(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 23.12/23.31  cnf(c_0_50, plain, (v1_xboole_0(X1)|m1_subset_1(k3_xboole_0(X2,X3),X1)|~r2_hidden(k3_xboole_0(X2,X3),X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_38]), c_0_34]), c_0_38]), c_0_38])])).
% 23.12/23.31  cnf(c_0_51, negated_conjecture, (r2_hidden(k3_xboole_0(X1,X2),esk5_0)|~r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 23.12/23.31  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 23.12/23.31  fof(c_0_53, plain, ![X12, X13]:(~m1_subset_1(X12,X13)|(v1_xboole_0(X13)|r2_hidden(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 23.12/23.31  fof(c_0_54, plain, ![X25, X26, X28, X29, X30]:((((m1_subset_1(esk1_2(X25,X26),u1_struct_0(X25))|~r2_yellow_0(X25,X26)|(~v5_orders_2(X25)|~l1_orders_2(X25)))&(r1_lattice3(X25,X26,esk1_2(X25,X26))|~r2_yellow_0(X25,X26)|(~v5_orders_2(X25)|~l1_orders_2(X25))))&(~m1_subset_1(X28,u1_struct_0(X25))|(~r1_lattice3(X25,X26,X28)|r1_orders_2(X25,X28,esk1_2(X25,X26)))|~r2_yellow_0(X25,X26)|(~v5_orders_2(X25)|~l1_orders_2(X25))))&((m1_subset_1(esk2_3(X25,X29,X30),u1_struct_0(X25))|(~m1_subset_1(X30,u1_struct_0(X25))|~r1_lattice3(X25,X29,X30))|r2_yellow_0(X25,X29)|(~v5_orders_2(X25)|~l1_orders_2(X25)))&((r1_lattice3(X25,X29,esk2_3(X25,X29,X30))|(~m1_subset_1(X30,u1_struct_0(X25))|~r1_lattice3(X25,X29,X30))|r2_yellow_0(X25,X29)|(~v5_orders_2(X25)|~l1_orders_2(X25)))&(~r1_orders_2(X25,esk2_3(X25,X29,X30),X30)|(~m1_subset_1(X30,u1_struct_0(X25))|~r1_lattice3(X25,X29,X30))|r2_yellow_0(X25,X29)|(~v5_orders_2(X25)|~l1_orders_2(X25)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).
% 23.12/23.31  cnf(c_0_55, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 23.12/23.31  cnf(c_0_56, plain, (r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_38]), c_0_38])).
% 23.12/23.31  cnf(c_0_57, plain, (v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_48, c_0_28])).
% 23.12/23.31  cnf(c_0_58, plain, (v1_xboole_0(X1)|~v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_49, c_0_28])).
% 23.12/23.31  cnf(c_0_59, plain, (v5_orders_2(k2_yellow_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 23.12/23.31  cnf(c_0_60, negated_conjecture, (m1_subset_1(k3_xboole_0(X1,X2),esk5_0)|~r2_hidden(X2,esk5_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 23.12/23.31  cnf(c_0_61, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 23.12/23.31  fof(c_0_62, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)<=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), introduced(definition)).
% 23.12/23.31  cnf(c_0_63, plain, (r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 23.12/23.31  cnf(c_0_64, plain, (r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|v1_xboole_0(X1)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_34]), c_0_38]), c_0_38])]), c_0_58])).
% 23.12/23.31  cnf(c_0_65, plain, (v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))), inference(rw,[status(thm)],[c_0_59, c_0_28])).
% 23.12/23.31  cnf(c_0_66, negated_conjecture, (m1_subset_1(k3_xboole_0(X1,X2),esk5_0)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_52])).
% 23.12/23.31  fof(c_0_67, plain, ![X1, X4, X3, X2]:(epred1_4(X2,X3,X4,X1)=>((((r1_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4)))&((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X2,X4))=>r1_lattice3(X1,k2_tarski(X3,X4),X2)))&(r2_lattice3(X1,k2_tarski(X3,X4),X2)=>(r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))))&((r1_orders_2(X1,X3,X2)&r1_orders_2(X1,X4,X2))=>r2_lattice3(X1,k2_tarski(X3,X4),X2)))), inference(split_equiv,[status(thm)],[c_0_62])).
% 23.12/23.31  cnf(c_0_68, plain, (r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),X2)|v1_xboole_0(X1)|~r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3),X1)|~m1_subset_1(X3,X1)|~r1_tarski(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3),X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_34]), c_0_38])])).
% 23.12/23.31  cnf(c_0_69, negated_conjecture, (m1_subset_1(k3_xboole_0(X1,X2),esk5_0)|~m1_subset_1(X2,esk5_0)|~m1_subset_1(X1,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_61]), c_0_52])).
% 23.12/23.31  fof(c_0_70, plain, ![X9, X10, X11]:(~r1_tarski(X9,X10)|~r1_tarski(X9,X11)|r1_tarski(X9,k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 23.12/23.31  fof(c_0_71, plain, ![X32, X33, X34]:((~v2_lattice3(X32)|(~m1_subset_1(X33,u1_struct_0(X32))|(~m1_subset_1(X34,u1_struct_0(X32))|r2_yellow_0(X32,k2_tarski(X33,X34))))|(~v5_orders_2(X32)|~l1_orders_2(X32)))&((m1_subset_1(esk3_1(X32),u1_struct_0(X32))|v2_lattice3(X32)|(~v5_orders_2(X32)|~l1_orders_2(X32)))&((m1_subset_1(esk4_1(X32),u1_struct_0(X32))|v2_lattice3(X32)|(~v5_orders_2(X32)|~l1_orders_2(X32)))&(~r2_yellow_0(X32,k2_tarski(esk3_1(X32),esk4_1(X32)))|v2_lattice3(X32)|(~v5_orders_2(X32)|~l1_orders_2(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).
% 23.12/23.31  cnf(c_0_72, plain, (r1_tarski(X2,X3)|v1_xboole_0(X1)|~r3_orders_2(k2_yellow_1(X1),X2,X3)|~m1_subset_1(X3,u1_struct_0(k2_yellow_1(X1)))|~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 23.12/23.31  fof(c_0_73, plain, ![X55, X56, X57, X58]:(((((r1_orders_2(X55,X58,X57)|~r1_lattice3(X55,k2_tarski(X57,X56),X58)|~epred1_4(X58,X57,X56,X55))&(r1_orders_2(X55,X58,X56)|~r1_lattice3(X55,k2_tarski(X57,X56),X58)|~epred1_4(X58,X57,X56,X55)))&(~r1_orders_2(X55,X58,X57)|~r1_orders_2(X55,X58,X56)|r1_lattice3(X55,k2_tarski(X57,X56),X58)|~epred1_4(X58,X57,X56,X55)))&((r1_orders_2(X55,X57,X58)|~r2_lattice3(X55,k2_tarski(X57,X56),X58)|~epred1_4(X58,X57,X56,X55))&(r1_orders_2(X55,X56,X58)|~r2_lattice3(X55,k2_tarski(X57,X56),X58)|~epred1_4(X58,X57,X56,X55))))&(~r1_orders_2(X55,X57,X58)|~r1_orders_2(X55,X56,X58)|r2_lattice3(X55,k2_tarski(X57,X56),X58)|~epred1_4(X58,X57,X56,X55))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_67])])])).
% 23.12/23.31  fof(c_0_74, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>epred1_4(X2,X3,X4,X1))))), inference(apply_def,[status(thm)],[t8_yellow_0, c_0_62])).
% 23.12/23.31  cnf(c_0_75, negated_conjecture, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)|~r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3))|~m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),esk5_0)|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X2,esk5_0)|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),k3_xboole_0(X2,X3))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_52])).
% 23.12/23.31  cnf(c_0_76, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 23.12/23.31  cnf(c_0_77, plain, (m1_subset_1(esk4_1(X1),u1_struct_0(X1))|v2_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 23.12/23.31  cnf(c_0_78, negated_conjecture, (~v2_lattice3(k2_yellow_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 23.12/23.31  cnf(c_0_79, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))|~m1_subset_1(X2,u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_28]), c_0_28]), c_0_28])).
% 23.12/23.31  cnf(c_0_80, plain, (r1_orders_2(X1,X2,X3)|~r1_lattice3(X1,k2_tarski(X4,X3),X2)|~epred1_4(X2,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 23.12/23.31  cnf(c_0_81, plain, (r1_lattice3(X1,X2,esk2_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 23.12/23.31  fof(c_0_82, plain, ![X37, X38, X39, X40]:(~l1_orders_2(X37)|(~m1_subset_1(X38,u1_struct_0(X37))|(~m1_subset_1(X39,u1_struct_0(X37))|(~m1_subset_1(X40,u1_struct_0(X37))|epred1_4(X38,X39,X40,X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_74])])])).
% 23.12/23.31  cnf(c_0_83, negated_conjecture, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)|~r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3))|~m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),esk5_0)|~m1_subset_1(X3,esk5_0)|~m1_subset_1(X2,esk5_0)|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),X3)|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 23.12/23.31  cnf(c_0_84, plain, (v2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))|m1_subset_1(esk4_1(g1_orders_2(X1,k1_yellow_1(X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_38]), c_0_65]), c_0_34])])).
% 23.12/23.31  cnf(c_0_85, negated_conjecture, (~v2_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))), inference(rw,[status(thm)],[c_0_78, c_0_28])).
% 23.12/23.31  cnf(c_0_86, plain, (m1_subset_1(esk3_1(X1),u1_struct_0(X1))|v2_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 23.12/23.31  cnf(c_0_87, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_38]), c_0_38])).
% 23.12/23.31  cnf(c_0_88, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 23.12/23.31  cnf(c_0_89, plain, (r2_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X3)|~epred1_4(esk2_3(X1,k2_tarski(X2,X3),X4),X2,X3,X1)|~r1_lattice3(X1,k2_tarski(X2,X3),X4)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 23.12/23.31  cnf(c_0_90, plain, (epred1_4(X2,X3,X4,X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 23.12/23.31  cnf(c_0_91, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 23.12/23.31  cnf(c_0_92, plain, (r1_orders_2(X1,X2,X3)|~r1_lattice3(X1,k2_tarski(X3,X4),X2)|~epred1_4(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 23.12/23.31  cnf(c_0_93, negated_conjecture, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)|~r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk5_0)|~m1_subset_1(X2,esk5_0)|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(X2,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_85])).
% 23.12/23.31  cnf(c_0_94, plain, (v2_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))|m1_subset_1(esk3_1(g1_orders_2(X1,k1_yellow_1(X1))),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_38]), c_0_65]), c_0_34])])).
% 23.12/23.31  cnf(c_0_95, plain, (v1_xboole_0(X1)|r1_tarski(X2,X3)|~r1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_57]), c_0_34]), c_0_38]), c_0_38])]), c_0_58])).
% 23.12/23.31  cnf(c_0_96, plain, (r2_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X3)|~r1_lattice3(X1,k2_tarski(X2,X3),X4)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 23.12/23.31  cnf(c_0_97, plain, (r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),X2)|m1_subset_1(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3),X1)|~r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),X2,X3)|~m1_subset_1(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_38]), c_0_65]), c_0_34])])).
% 23.12/23.31  cnf(c_0_98, plain, (r2_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X2)|~epred1_4(esk2_3(X1,k2_tarski(X2,X3),X4),X2,X3,X1)|~r1_lattice3(X1,k2_tarski(X2,X3),X4)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_92, c_0_81])).
% 23.12/23.31  cnf(c_0_99, negated_conjecture, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1)|~r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~m1_subset_1(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk5_0)|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),X1,k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_85])).
% 23.12/23.31  cnf(c_0_100, plain, (r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3))|v1_xboole_0(X1)|r1_tarski(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4),X3)|~r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4)|~m1_subset_1(X3,X1)|~m1_subset_1(X4,X1)|~m1_subset_1(X2,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_65]), c_0_34]), c_0_38]), c_0_38]), c_0_38])]), c_0_97])).
% 23.12/23.31  cnf(c_0_101, plain, (r2_yellow_0(X1,k2_tarski(X2,X3))|r1_orders_2(X1,esk2_3(X1,k2_tarski(X2,X3),X4),X2)|~r1_lattice3(X1,k2_tarski(X2,X3),X4)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_90]), c_0_91])).
% 23.12/23.31  cnf(c_0_102, negated_conjecture, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(X1,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(X1,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~m1_subset_1(k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk5_0)|~m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)|~m1_subset_1(X1,esk5_0)|~r1_tarski(esk2_3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(X1,esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_52]), c_0_97])).
% 23.12/23.31  cnf(c_0_103, plain, (r2_yellow_0(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3))|v1_xboole_0(X1)|r1_tarski(esk2_3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4),X2)|~r1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)),k2_tarski(X2,X3),X4)|~m1_subset_1(X2,X1)|~m1_subset_1(X4,X1)|~m1_subset_1(X3,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_101]), c_0_65]), c_0_34]), c_0_38]), c_0_38]), c_0_38])]), c_0_97])).
% 23.12/23.31  cnf(c_0_104, plain, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~r1_lattice3(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)|~m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_52]), c_0_69])).
% 23.12/23.31  cnf(c_0_105, plain, (r1_lattice3(X1,k2_tarski(X3,X4),X2)|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X2,X4)|~epred1_4(X2,X3,X4,X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 23.12/23.31  fof(c_0_106, plain, ![X7, X8]:r1_tarski(k3_xboole_0(X7,X8),X7), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 23.12/23.31  fof(c_0_107, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 23.12/23.31  cnf(c_0_108, plain, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~epred1_4(k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))|~r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))|~r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))|~m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)|~m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 23.12/23.31  cnf(c_0_109, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 23.12/23.31  cnf(c_0_110, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 23.12/23.31  cnf(c_0_111, plain, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))|~r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))|~m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)|~m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_90]), c_0_34]), c_0_38]), c_0_38]), c_0_38])]), c_0_69])).
% 23.12/23.31  cnf(c_0_112, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 23.12/23.31  cnf(c_0_113, plain, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~r1_orders_2(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k3_xboole_0(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))),esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))))|~m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)|~m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_64]), c_0_112])]), c_0_52]), c_0_69])).
% 23.12/23.31  cnf(c_0_114, plain, (v2_lattice3(X1)|~r2_yellow_0(X1,k2_tarski(esk3_1(X1),esk4_1(X1)))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 23.12/23.31  cnf(c_0_115, plain, (r2_yellow_0(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)),k2_tarski(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0)))))|~m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)|~m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_64]), c_0_109])]), c_0_52]), c_0_69])).
% 23.12/23.31  cnf(c_0_116, plain, (~m1_subset_1(esk4_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)|~m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_65]), c_0_34])]), c_0_85])).
% 23.12/23.31  cnf(c_0_117, plain, (~m1_subset_1(esk3_1(g1_orders_2(esk5_0,k1_yellow_1(esk5_0))),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_84]), c_0_85])).
% 23.12/23.31  cnf(c_0_118, plain, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_94]), c_0_85]), ['proof']).
% 23.12/23.31  # SZS output end CNFRefutation
% 23.12/23.31  # Proof object total steps             : 119
% 23.12/23.31  # Proof object clause steps            : 76
% 23.12/23.31  # Proof object formula steps           : 43
% 23.12/23.31  # Proof object conjectures             : 15
% 23.12/23.31  # Proof object clause conjectures      : 12
% 23.12/23.31  # Proof object formula conjectures     : 3
% 23.12/23.31  # Proof object initial clauses used    : 32
% 23.12/23.31  # Proof object initial formulas used   : 19
% 23.12/23.31  # Proof object generating inferences   : 32
% 23.12/23.31  # Proof object simplifying inferences  : 101
% 23.12/23.31  # Training examples: 0 positive, 0 negative
% 23.12/23.31  # Parsed axioms                        : 19
% 23.12/23.31  # Removed by relevancy pruning/SinE    : 0
% 23.12/23.31  # Initial clauses                      : 47
% 23.12/23.31  # Removed in clause preprocessing      : 1
% 23.12/23.31  # Initial clauses in saturation        : 46
% 23.12/23.31  # Processed clauses                    : 13253
% 23.12/23.31  # ...of these trivial                  : 4
% 23.12/23.31  # ...subsumed                          : 5839
% 23.12/23.31  # ...remaining for further processing  : 7410
% 23.12/23.31  # Other redundant clauses eliminated   : 12
% 23.12/23.31  # Clauses deleted for lack of memory   : 0
% 23.12/23.31  # Backward-subsumed                    : 141
% 23.12/23.31  # Backward-rewritten                   : 0
% 23.12/23.31  # Generated clauses                    : 880548
% 23.12/23.31  # ...of the previous two non-trivial   : 880497
% 23.12/23.31  # Contextual simplify-reflections      : 105
% 23.12/23.31  # Paramodulations                      : 880524
% 23.12/23.31  # Factorizations                       : 0
% 23.12/23.31  # Equation resolutions                 : 24
% 23.12/23.31  # Propositional unsat checks           : 0
% 23.12/23.31  #    Propositional check models        : 0
% 23.12/23.31  #    Propositional check unsatisfiable : 0
% 23.12/23.31  #    Propositional clauses             : 0
% 23.12/23.31  #    Propositional clauses after purity: 0
% 23.12/23.31  #    Propositional unsat core size     : 0
% 23.12/23.31  #    Propositional preprocessing time  : 0.000
% 23.12/23.31  #    Propositional encoding time       : 0.000
% 23.12/23.31  #    Propositional solver time         : 0.000
% 23.12/23.31  #    Success case prop preproc time    : 0.000
% 23.12/23.31  #    Success case prop encoding time   : 0.000
% 23.12/23.31  #    Success case prop solver time     : 0.000
% 23.12/23.31  # Current number of processed clauses  : 7225
% 23.12/23.31  #    Positive orientable unit clauses  : 14
% 23.12/23.31  #    Positive unorientable unit clauses: 1
% 23.12/23.31  #    Negative unit clauses             : 3
% 23.12/23.31  #    Non-unit-clauses                  : 7207
% 23.12/23.31  # Current number of unprocessed clauses: 866904
% 23.12/23.31  # ...number of literals in the above   : 6458777
% 23.12/23.31  # Current number of archived formulas  : 0
% 23.12/23.31  # Current number of archived clauses   : 186
% 23.12/23.31  # Clause-clause subsumption calls (NU) : 8670061
% 23.12/23.31  # Rec. Clause-clause subsumption calls : 167585
% 23.12/23.31  # Non-unit clause-clause subsumptions  : 6022
% 23.12/23.31  # Unit Clause-clause subsumption calls : 5591
% 23.12/23.31  # Rewrite failures with RHS unbound    : 0
% 23.12/23.31  # BW rewrite match attempts            : 5
% 23.12/23.31  # BW rewrite match successes           : 4
% 23.12/23.31  # Condensation attempts                : 0
% 23.12/23.31  # Condensation successes               : 0
% 23.12/23.31  # Termbank termtop insertions          : 162855317
% 23.16/23.37  
% 23.16/23.37  # -------------------------------------------------
% 23.16/23.37  # User time                : 22.441 s
% 23.16/23.37  # System time              : 0.583 s
% 23.16/23.37  # Total time               : 23.025 s
% 23.16/23.37  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
