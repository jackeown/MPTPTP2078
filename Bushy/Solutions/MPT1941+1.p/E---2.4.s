%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t39_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:55 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 464 expanded)
%              Number of clauses        :   51 ( 188 expanded)
%              Number of leaves         :   14 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  330 (2341 expanded)
%              Number of equality atoms :   36 ( 224 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',free_g1_orders_2)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',dt_k1_yellow_1)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',abstractness_v1_orders_2)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',dt_k2_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',d1_yellow_1)).

fof(d17_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k9_yellow_6(X1,X2) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',d17_yellow_6)).

fof(fraenkel_a_2_0_yellow_6,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_0_yellow_6(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = X4
            & r2_hidden(X3,X4)
            & v3_pre_topc(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',fraenkel_a_2_0_yellow_6)).

fof(t12_yellow_6,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => u1_struct_0(X1) = u1_struct_0(k7_lattice3(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',t12_yellow_6)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',t4_subset)).

fof(t39_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
              <=> ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',t39_yellow_6)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',t1_subset)).

fof(t38_yellow_6,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
             => ? [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                  & X4 = X3
                  & r2_hidden(X2,X4)
                  & v3_pre_topc(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',t38_yellow_6)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t39_yellow_6.p',t2_subset)).

fof(c_0_14,plain,(
    ! [X35,X36,X37,X38] :
      ( ( X35 = X37
        | g1_orders_2(X35,X36) != g1_orders_2(X37,X38)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X35,X35))) )
      & ( X36 = X38
        | g1_orders_2(X35,X36) != g1_orders_2(X37,X38)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X35,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_15,plain,(
    ! [X17] :
      ( v1_relat_2(k1_yellow_1(X17))
      & v4_relat_2(k1_yellow_1(X17))
      & v8_relat_2(k1_yellow_1(X17))
      & v1_partfun1(k1_yellow_1(X17),X17)
      & m1_subset_1(k1_yellow_1(X17),k1_zfmisc_1(k2_zfmisc_1(X17,X17))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

cnf(c_0_16,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | ~ v1_orders_2(X8)
      | X8 = g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_19,plain,(
    ! [X18] :
      ( v1_orders_2(k2_yellow_1(X18))
      & l1_orders_2(k2_yellow_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_20,plain,(
    ! [X13] : k2_yellow_1(X13) = g1_orders_2(X13,k1_yellow_1(X13)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_21,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | k9_yellow_6(X11,X12) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X11,X12))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_yellow_6])])])])).

cnf(c_0_22,plain,
    ( X1 = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X30,X31,X32,X34] :
      ( ( m1_subset_1(esk8_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r2_hidden(X30,a_2_0_yellow_6(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( X30 = esk8_3(X30,X31,X32)
        | ~ r2_hidden(X30,a_2_0_yellow_6(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( r2_hidden(X32,esk8_3(X30,X31,X32))
        | ~ r2_hidden(X30,a_2_0_yellow_6(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( v3_pre_topc(esk8_3(X30,X31,X32),X31)
        | ~ r2_hidden(X30,a_2_0_yellow_6(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X31)))
        | X30 != X34
        | ~ r2_hidden(X32,X34)
        | ~ v3_pre_topc(X34,X31)
        | r2_hidden(X30,a_2_0_yellow_6(X31,X32))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | ~ m1_subset_1(X32,u1_struct_0(X31)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_yellow_6])])])])])])).

fof(c_0_28,plain,(
    ! [X40] :
      ( ~ l1_orders_2(X40)
      | u1_struct_0(X40) = u1_struct_0(k7_lattice3(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_yellow_6])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | k9_yellow_6(X1,X2) = k7_lattice3(k2_yellow_1(a_2_0_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( X1 = u1_struct_0(X2)
    | g1_orders_2(X1,k1_yellow_1(X1)) != X2
    | ~ v1_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

fof(c_0_33,plain,(
    ! [X54,X55,X56] :
      ( ~ r2_hidden(X54,X55)
      | ~ m1_subset_1(X55,k1_zfmisc_1(X56))
      | m1_subset_1(X54,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_34,plain,
    ( v3_pre_topc(esk8_3(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow_6(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( X1 = esk8_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow_6(X2,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( u1_struct_0(X1) = u1_struct_0(k7_lattice3(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k9_yellow_6(X1,X2) = k7_lattice3(g1_orders_2(a_2_0_yellow_6(X1,X2),k1_yellow_1(a_2_0_yellow_6(X1,X2))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_38,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31]),c_0_32])])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,u1_struct_0(k9_yellow_6(X1,X2)))
                <=> ( r2_hidden(X2,X3)
                    & v3_pre_topc(X3,X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t39_yellow_6])).

fof(c_0_40,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | m1_subset_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,a_2_0_yellow_6(X2,X4))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != X1
    | ~ r2_hidden(X4,X1)
    | ~ v3_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_yellow_6(X2,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,plain,
    ( a_2_0_yellow_6(X1,X2) = u1_struct_0(k9_yellow_6(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])]),c_0_38])).

fof(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0)))
      | ~ r2_hidden(esk2_0,esk3_0)
      | ~ v3_pre_topc(esk3_0,esk1_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) )
    & ( v3_pre_topc(esk3_0,esk1_0)
      | r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_39])])])])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,a_2_0_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_41,c_0_42])])).

cnf(c_0_48,plain,
    ( v3_pre_topc(X1,X2)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0)
    | r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_54,plain,(
    ! [X48,X49,X50] :
      ( ( m1_subset_1(esk10_3(X48,X49,X50),k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X50,u1_struct_0(k9_yellow_6(X48,X49)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( esk10_3(X48,X49,X50) = X50
        | ~ m1_subset_1(X50,u1_struct_0(k9_yellow_6(X48,X49)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( r2_hidden(X49,esk10_3(X48,X49,X50))
        | ~ m1_subset_1(X50,u1_struct_0(k9_yellow_6(X48,X49)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( v3_pre_topc(esk10_3(X48,X49,X50),X48)
        | ~ m1_subset_1(X50,u1_struct_0(k9_yellow_6(X48,X49)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_6])])])])])])).

fof(c_0_55,plain,(
    ! [X61,X62] :
      ( ~ r2_hidden(X61,X62)
      | ~ v1_xboole_0(X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_56,plain,
    ( m1_subset_1(X1,a_2_0_yellow_6(X2,X3))
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,esk10_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( esk10_3(X1,X2,X3) = X3
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_63,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk3_0,a_2_0_yellow_6(esk1_0,X1))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | m1_subset_1(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_61])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(a_2_0_yellow_6(X1,X2))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_47])).

cnf(c_0_69,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,X1)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_44]),c_0_51]),c_0_52])]),c_0_53]),c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0)))
    | ~ r2_hidden(esk2_0,esk3_0)
    | ~ v3_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_50]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v3_pre_topc(X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_44]),c_0_42])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(esk1_0,X1)))
    | r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,X1)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk1_0)
    | ~ r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,X1)))
    | ~ v3_pre_topc(X2,esk1_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_51]),c_0_52])]),c_0_53])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_57])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(k9_yellow_6(esk1_0,X1)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_57]),c_0_58])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
