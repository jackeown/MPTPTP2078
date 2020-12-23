%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_6__t13_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 151.26s
% Output     : CNFRefutation 151.26s
% Verified   : 
% Statistics : Number of formulae       :   40 (  92 expanded)
%              Number of clauses        :   23 (  35 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 374 expanded)
%              Number of equality atoms :   31 (  69 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   25 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_yellow_6,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => u1_struct_0(k3_yellow_6(X1,X2,X3)) = u1_struct_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',t13_yellow_6)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',free_g1_orders_2)).

fof(abstractness_v1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_orders_2(X1)
       => X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',abstractness_v1_orders_2)).

fof(dt_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ( v1_orders_2(g1_orders_2(X1,X2))
        & l1_orders_2(g1_orders_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',dt_g1_orders_2)).

fof(d7_yellow_6,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X2)
                    & l1_waybel_0(X4,X2) )
                 => ( X4 = k3_yellow_6(X1,X2,X3)
                  <=> ( g1_orders_2(u1_struct_0(X4),u1_orders_2(X4)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
                      & r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),u1_waybel_0(X2,X4),k8_funcop_1(u1_struct_0(X2),u1_struct_0(X4),X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',d7_yellow_6)).

fof(dt_k3_yellow_6,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)
        & l1_waybel_0(k3_yellow_6(X1,X2,X3),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',dt_k3_yellow_6)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',dt_u1_orders_2)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t13_yellow_6.p',dt_l1_waybel_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => u1_struct_0(k3_yellow_6(X1,X2,X3)) = u1_struct_0(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_yellow_6])).

fof(c_0_9,plain,(
    ! [X45,X46,X47,X48] :
      ( ( X45 = X47
        | g1_orders_2(X45,X46) != g1_orders_2(X47,X48)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X45))) )
      & ( X46 = X48
        | g1_orders_2(X45,X46) != g1_orders_2(X47,X48)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X45,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_10,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | ~ v1_orders_2(X12)
      | X12 = g1_orders_2(u1_struct_0(X12),u1_orders_2(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_orders_2])])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ( v1_orders_2(g1_orders_2(X21,X22))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21))) )
      & ( l1_orders_2(g1_orders_2(X21,X22))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X21,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_orders_2])])])).

fof(c_0_12,plain,(
    ! [X17,X18,X19,X20] :
      ( ( g1_orders_2(u1_struct_0(X20),u1_orders_2(X20)) = g1_orders_2(u1_struct_0(X17),u1_orders_2(X17))
        | X20 != k3_yellow_6(X17,X18,X19)
        | ~ v6_waybel_0(X20,X18)
        | ~ l1_waybel_0(X20,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | ~ l1_orders_2(X17) )
      & ( r2_funct_2(u1_struct_0(X20),u1_struct_0(X18),u1_waybel_0(X18,X20),k8_funcop_1(u1_struct_0(X18),u1_struct_0(X20),X19))
        | X20 != k3_yellow_6(X17,X18,X19)
        | ~ v6_waybel_0(X20,X18)
        | ~ l1_waybel_0(X20,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | ~ l1_orders_2(X17) )
      & ( g1_orders_2(u1_struct_0(X20),u1_orders_2(X20)) != g1_orders_2(u1_struct_0(X17),u1_orders_2(X17))
        | ~ r2_funct_2(u1_struct_0(X20),u1_struct_0(X18),u1_waybel_0(X18,X20),k8_funcop_1(u1_struct_0(X18),u1_struct_0(X20),X19))
        | X20 = k3_yellow_6(X17,X18,X19)
        | ~ v6_waybel_0(X20,X18)
        | ~ l1_waybel_0(X20,X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_yellow_6])])])])])).

fof(c_0_13,plain,(
    ! [X27,X28,X29] :
      ( ( v6_waybel_0(k3_yellow_6(X27,X28,X29),X28)
        | ~ l1_orders_2(X27)
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) )
      & ( l1_waybel_0(k3_yellow_6(X27,X28,X29),X28)
        | ~ l1_orders_2(X27)
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_yellow_6])])])])).

fof(c_0_14,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0)) != u1_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( X1 = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( l1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_orders_2(g1_orders_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X36] :
      ( ~ l1_orders_2(X36)
      | m1_subset_1(u1_orders_2(X36),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X36)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_20,plain,
    ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | v2_struct_0(X3)
    | X1 != k3_yellow_6(X2,X3,X4)
    | ~ v6_waybel_0(X1,X3)
    | ~ l1_waybel_0(X1,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_struct_0(X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( l1_waybel_0(k3_yellow_6(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v6_waybel_0(k3_yellow_6(X1,X2,X3),X2)
    | v2_struct_0(X2)
    | ~ l1_orders_2(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_23,plain,(
    ! [X34,X35] :
      ( ~ l1_struct_0(X34)
      | ~ l1_waybel_0(X35,X34)
      | l1_orders_2(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,plain,
    ( u1_struct_0(g1_orders_2(X1,X2)) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_28,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(X1,X2,X3)),u1_orders_2(k3_yellow_6(X1,X2,X3))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_30,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( l1_waybel_0(k3_yellow_6(X1,esk2_0,esk3_0),esk2_0)
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_32,plain,
    ( u1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( g1_orders_2(u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0)),u1_orders_2(k3_yellow_6(X1,esk2_0,esk3_0))) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( l1_orders_2(k3_yellow_6(X1,esk2_0,esk3_0))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_25])])).

cnf(c_0_35,negated_conjecture,
    ( u1_struct_0(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) = u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_36,negated_conjecture,
    ( u1_struct_0(k3_yellow_6(esk1_0,esk2_0,esk3_0)) != u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(k3_yellow_6(X1,esk2_0,esk3_0)) = u1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
