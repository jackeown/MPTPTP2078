%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t25_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:05 EDT 2019

% Result     : Theorem 285.06s
% Output     : CNFRefutation 285.06s
% Verified   : 
% Statistics : Number of formulae       :  101 (4892 expanded)
%              Number of clauses        :   72 (2115 expanded)
%              Number of leaves         :   14 (1347 expanded)
%              Depth                    :   17
%              Number of atoms          :  439 (12747 expanded)
%              Number of equality atoms :   30 (3364 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   54 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',redefinition_k9_setfam_1)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',free_g1_orders_2)).

fof(dt_k1_yellow_1,axiom,(
    ! [X1] :
      ( v1_relat_2(k1_yellow_1(X1))
      & v4_relat_2(k1_yellow_1(X1))
      & v8_relat_2(k1_yellow_1(X1))
      & v1_partfun1(k1_yellow_1(X1),X1)
      & m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',dt_k1_yellow_1)).

fof(dt_k2_yellow_1,axiom,(
    ! [X1] :
      ( v1_orders_2(k2_yellow_1(X1))
      & l1_orders_2(k2_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',dt_k2_yellow_1)).

fof(d1_yellow_1,axiom,(
    ! [X1] : k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',d1_yellow_1)).

fof(t9_waybel_7,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
     => k7_waybel_1(k3_yellow_1(X1),X2) = k6_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',t9_waybel_7)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',abstractness_v1_orders_2)).

fof(t25_waybel_7,conjecture,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X2)
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
     => ( v2_waybel_7(X2,k3_yellow_1(X1))
      <=> ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r2_hidden(X3,X2)
              | r2_hidden(k6_subset_1(X1,X3),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',t25_waybel_7)).

fof(t24_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v11_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_7(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,X2)
                  | r2_hidden(k7_waybel_1(X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',t24_waybel_7)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',t7_boole)).

fof(fc1_waybel_7,axiom,(
    ! [X1] :
      ( v1_orders_2(k3_yellow_1(X1))
      & v11_waybel_1(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',fc1_waybel_7)).

fof(fc7_yellow_1,axiom,(
    ! [X1] :
      ( ~ v2_struct_0(k3_yellow_1(X1))
      & v1_orders_2(k3_yellow_1(X1))
      & v3_orders_2(k3_yellow_1(X1))
      & v4_orders_2(k3_yellow_1(X1))
      & v5_orders_2(k3_yellow_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',fc7_yellow_1)).

fof(cc8_waybel_1,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( ( ~ v2_struct_0(X1)
          & v11_waybel_1(X1) )
       => ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & v3_yellow_0(X1)
          & v2_waybel_1(X1)
          & v10_waybel_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t25_waybel_7.p',cc8_waybel_1)).

fof(c_0_14,plain,(
    ! [X69] : k3_yellow_1(X69) = k2_yellow_1(k9_setfam_1(X69)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_15,plain,(
    ! [X53] : k9_setfam_1(X53) = k1_zfmisc_1(X53) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

fof(c_0_16,plain,(
    ! [X42,X43,X44,X45] :
      ( ( X42 = X44
        | g1_orders_2(X42,X43) != g1_orders_2(X44,X45)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))) )
      & ( X43 = X45
        | g1_orders_2(X42,X43) != g1_orders_2(X44,X45)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_17,plain,(
    ! [X18] :
      ( v1_relat_2(k1_yellow_1(X18))
      & v4_relat_2(k1_yellow_1(X18))
      & v8_relat_2(k1_yellow_1(X18))
      & v1_partfun1(k1_yellow_1(X18),X18)
      & m1_subset_1(k1_yellow_1(X18),k1_zfmisc_1(k2_zfmisc_1(X18,X18))) ) ),
    inference(variable_rename,[status(thm)],[dt_k1_yellow_1])).

fof(c_0_18,plain,(
    ! [X19] :
      ( v1_orders_2(k2_yellow_1(X19))
      & l1_orders_2(k2_yellow_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[dt_k2_yellow_1])).

fof(c_0_19,plain,(
    ! [X12] : k2_yellow_1(X12) = g1_orders_2(X12,k1_yellow_1(X12)) ),
    inference(variable_rename,[status(thm)],[d1_yellow_1])).

fof(c_0_20,plain,(
    ! [X78,X79] :
      ( ~ m1_subset_1(X79,u1_struct_0(k3_yellow_1(X78)))
      | k7_waybel_1(k3_yellow_1(X78),X79) = k6_subset_1(X78,X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_waybel_7])])).

cnf(c_0_21,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(k1_yellow_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X9] :
      ( ~ l1_orders_2(X9)
      | ~ v1_orders_2(X9)
      | X9 = g1_orders_2(u1_struct_0(X9),u1_orders_2(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

cnf(c_0_26,plain,
    ( v1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_yellow_1(X1) = g1_orders_2(X1,k1_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( l1_orders_2(k2_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v1_xboole_0(X2)
          & v2_waybel_0(X2,k3_yellow_1(X1))
          & v13_waybel_0(X2,k3_yellow_1(X1))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) )
       => ( v2_waybel_7(X2,k3_yellow_1(X1))
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X1))
             => ( r2_hidden(X3,X2)
                | r2_hidden(k6_subset_1(X1,X3),X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t25_waybel_7])).

fof(c_0_30,plain,(
    ! [X56,X57,X58] :
      ( ( ~ v2_waybel_7(X57,X56)
        | ~ m1_subset_1(X58,u1_struct_0(X56))
        | r2_hidden(X58,X57)
        | r2_hidden(k7_waybel_1(X56,X58),X57)
        | v1_xboole_0(X57)
        | ~ v2_waybel_0(X57,X56)
        | ~ v13_waybel_0(X57,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_orders_2(X56)
        | ~ v4_orders_2(X56)
        | ~ v5_orders_2(X56)
        | ~ v11_waybel_1(X56)
        | ~ v1_lattice3(X56)
        | ~ v2_lattice3(X56)
        | ~ l1_orders_2(X56) )
      & ( m1_subset_1(esk7_2(X56,X57),u1_struct_0(X56))
        | v2_waybel_7(X57,X56)
        | v1_xboole_0(X57)
        | ~ v2_waybel_0(X57,X56)
        | ~ v13_waybel_0(X57,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_orders_2(X56)
        | ~ v4_orders_2(X56)
        | ~ v5_orders_2(X56)
        | ~ v11_waybel_1(X56)
        | ~ v1_lattice3(X56)
        | ~ v2_lattice3(X56)
        | ~ l1_orders_2(X56) )
      & ( ~ r2_hidden(esk7_2(X56,X57),X57)
        | v2_waybel_7(X57,X56)
        | v1_xboole_0(X57)
        | ~ v2_waybel_0(X57,X56)
        | ~ v13_waybel_0(X57,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_orders_2(X56)
        | ~ v4_orders_2(X56)
        | ~ v5_orders_2(X56)
        | ~ v11_waybel_1(X56)
        | ~ v1_lattice3(X56)
        | ~ v2_lattice3(X56)
        | ~ l1_orders_2(X56) )
      & ( ~ r2_hidden(k7_waybel_1(X56,esk7_2(X56,X57)),X57)
        | v2_waybel_7(X57,X56)
        | v1_xboole_0(X57)
        | ~ v2_waybel_0(X57,X56)
        | ~ v13_waybel_0(X57,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
        | ~ v3_orders_2(X56)
        | ~ v4_orders_2(X56)
        | ~ v5_orders_2(X56)
        | ~ v11_waybel_1(X56)
        | ~ v1_lattice3(X56)
        | ~ v2_lattice3(X56)
        | ~ l1_orders_2(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_waybel_7])])])])])])).

fof(c_0_31,plain,(
    ! [X74,X75] :
      ( ~ r2_hidden(X74,X75)
      | ~ v1_xboole_0(X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_32,plain,
    ( k7_waybel_1(k3_yellow_1(X2),X1) = k6_subset_1(X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,plain,
    ( X1 = X2
    | g1_orders_2(X1,k1_yellow_1(X1)) != g1_orders_2(X2,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,plain,
    ( l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_27])).

fof(c_0_38,plain,(
    ! [X81] :
      ( v1_orders_2(k3_yellow_1(X81))
      & v11_waybel_1(k3_yellow_1(X81)) ) ),
    inference(variable_rename,[status(thm)],[fc1_waybel_7])).

fof(c_0_39,plain,(
    ! [X82] :
      ( ~ v2_struct_0(k3_yellow_1(X82))
      & v1_orders_2(k3_yellow_1(X82))
      & v3_orders_2(k3_yellow_1(X82))
      & v4_orders_2(k3_yellow_1(X82))
      & v5_orders_2(k3_yellow_1(X82)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc7_yellow_1])])).

fof(c_0_40,negated_conjecture,(
    ! [X8] :
      ( ~ v1_xboole_0(esk2_0)
      & v2_waybel_0(esk2_0,k3_yellow_1(esk1_0))
      & v13_waybel_0(esk2_0,k3_yellow_1(esk1_0))
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0))))
      & ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
        | ~ v2_waybel_7(esk2_0,k3_yellow_1(esk1_0)) )
      & ( ~ r2_hidden(esk3_0,esk2_0)
        | ~ v2_waybel_7(esk2_0,k3_yellow_1(esk1_0)) )
      & ( ~ r2_hidden(k6_subset_1(esk1_0,esk3_0),esk2_0)
        | ~ v2_waybel_7(esk2_0,k3_yellow_1(esk1_0)) )
      & ( v2_waybel_7(esk2_0,k3_yellow_1(esk1_0))
        | ~ m1_subset_1(X8,k1_zfmisc_1(esk1_0))
        | r2_hidden(X8,esk2_0)
        | r2_hidden(k6_subset_1(esk1_0,X8),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])])])).

cnf(c_0_41,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(k7_waybel_1(X1,esk7_2(X1,X2)),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( k7_waybel_1(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))),X1) = k6_subset_1(X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_33]),c_0_27]),c_0_27])).

cnf(c_0_44,plain,
    ( u1_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])]),c_0_36]),c_0_37])])).

cnf(c_0_45,plain,
    ( v11_waybel_1(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( v5_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( v4_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( v3_orders_2(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( v2_waybel_7(esk2_0,k3_yellow_1(esk1_0))
    | r2_hidden(X1,esk2_0)
    | r2_hidden(k6_subset_1(esk1_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( m1_subset_1(esk7_2(X1,X2),u1_struct_0(X1))
    | v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( v2_waybel_7(X1,X2)
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X2)
    | ~ v11_waybel_1(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(k7_waybel_1(X2,esk7_2(X2,X1)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v13_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_53,plain,
    ( k7_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X2) = k6_subset_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,plain,
    ( v11_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_33]),c_0_27])).

cnf(c_0_55,plain,
    ( v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_33]),c_0_27])).

cnf(c_0_56,plain,
    ( v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_33]),c_0_27])).

cnf(c_0_57,plain,
    ( v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_33]),c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | r2_hidden(k6_subset_1(esk1_0,X1),esk2_0)
    | v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_33]),c_0_27])).

cnf(c_0_59,plain,
    ( v2_waybel_7(X1,g1_orders_2(X2,k1_yellow_1(X2)))
    | m1_subset_1(esk7_2(g1_orders_2(X2,k1_yellow_1(X2)),X1),X2)
    | v1_xboole_0(X1)
    | ~ v2_lattice3(g1_orders_2(X2,k1_yellow_1(X2)))
    | ~ v1_lattice3(g1_orders_2(X2,k1_yellow_1(X2)))
    | ~ v11_waybel_1(g1_orders_2(X2,k1_yellow_1(X2)))
    | ~ v5_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))
    | ~ v4_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))
    | ~ v3_orders_2(g1_orders_2(X2,k1_yellow_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v13_waybel_0(X1,g1_orders_2(X2,k1_yellow_1(X2)))
    | ~ v2_waybel_0(X1,g1_orders_2(X2,k1_yellow_1(X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_44]),c_0_37])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_33]),c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( v13_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( v2_waybel_0(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_63,plain,
    ( v2_waybel_7(X1,g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))))
    | ~ r2_hidden(k6_subset_1(X2,esk7_2(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))),X1)),X1)
    | ~ m1_subset_1(esk7_2(g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))),X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ v13_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2))))
    | ~ v2_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X2),k1_yellow_1(k1_zfmisc_1(X2)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_37]),c_0_44])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k6_subset_1(esk1_0,esk7_2(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))),X1)),esk2_0)
    | r2_hidden(esk7_2(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))),X1),esk2_0)
    | v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | v2_waybel_7(X1,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | v1_xboole_0(X1)
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
    | ~ v13_waybel_0(X1,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v2_waybel_0(X1,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_54]),c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( v13_waybel_0(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_33]),c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( v2_waybel_0(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_33]),c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_69,plain,
    ( v2_waybel_7(X2,X1)
    | v1_xboole_0(X2)
    | ~ r2_hidden(esk7_2(X1,X2),X2)
    | ~ v2_waybel_0(X2,X1)
    | ~ v13_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v11_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk7_2(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))),esk2_0),esk2_0)
    | v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ m1_subset_1(esk7_2(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))),esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_67])]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    | ~ v2_waybel_7(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_72,plain,
    ( v2_waybel_7(X1,X2)
    | ~ v2_lattice3(X2)
    | ~ v1_lattice3(X2)
    | ~ v11_waybel_1(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(esk7_2(X2,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v13_waybel_0(X1,X2)
    | ~ v2_waybel_0(X1,X2) ),
    inference(csr,[status(thm)],[c_0_69,c_0_42])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk7_2(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))),esk2_0),esk2_0)
    | v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_59]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_65]),c_0_66]),c_0_67])]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(k6_subset_1(esk1_0,esk3_0),esk2_0)
    | ~ v2_waybel_7(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0)
    | ~ v2_waybel_7(esk2_0,k3_yellow_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    | ~ v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_33]),c_0_27])).

cnf(c_0_77,negated_conjecture,
    ( v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_37]),c_0_44]),c_0_65]),c_0_66]),c_0_67])])).

fof(c_0_78,plain,(
    ! [X80] :
      ( ( ~ v2_struct_0(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v3_orders_2(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v4_orders_2(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v5_orders_2(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v1_lattice3(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v2_lattice3(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v3_yellow_0(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v2_waybel_1(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) )
      & ( v10_waybel_1(X80)
        | v2_struct_0(X80)
        | ~ v11_waybel_1(X80)
        | ~ l1_orders_2(X80) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc8_waybel_1])])])])).

cnf(c_0_79,plain,
    ( ~ v2_struct_0(k3_yellow_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(k6_subset_1(esk1_0,esk3_0),esk2_0)
    | ~ v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_33]),c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0)
    | ~ v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_33]),c_0_27])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_83,plain,
    ( v2_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,plain,
    ( ~ v2_struct_0(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_33]),c_0_27])).

cnf(c_0_85,negated_conjecture,
    ( ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ r2_hidden(k6_subset_1(esk1_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_88,plain,
    ( v1_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v11_waybel_1(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ r2_hidden(k6_subset_1(esk1_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_83]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_83]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_91,plain,
    ( r2_hidden(X3,X1)
    | r2_hidden(k7_waybel_1(X2,X3),X1)
    | v1_xboole_0(X1)
    | ~ v2_waybel_7(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_waybel_0(X1,X2)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v11_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(k6_subset_1(esk1_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_88]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_88]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_95,plain,
    ( r2_hidden(k6_subset_1(X1,X2),X3)
    | r2_hidden(X2,X3)
    | v1_xboole_0(X3)
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
    | ~ v2_waybel_7(X3,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ v13_waybel_0(X3,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
    | ~ v2_waybel_0(X3,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_53]),c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_37]),c_0_44]),c_0_44])])).

cnf(c_0_96,negated_conjecture,
    ( v2_waybel_7(esk2_0,g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_92]),c_0_93]),c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k6_subset_1(esk1_0,X1),esk2_0)
    | r2_hidden(X1,esk2_0)
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_65]),c_0_66]),c_0_67])]),c_0_68])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k6_subset_1(esk1_0,X1),esk2_0)
    | r2_hidden(X1,esk2_0)
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(esk1_0),k1_yellow_1(k1_zfmisc_1(esk1_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_83]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k6_subset_1(esk1_0,X1),esk2_0)
    | r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_88]),c_0_54]),c_0_37])]),c_0_84])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_99]),c_0_92])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
