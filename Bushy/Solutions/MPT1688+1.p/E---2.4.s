%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t68_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 324 expanded)
%              Number of clauses        :   42 ( 100 expanded)
%              Number of leaves         :    6 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  303 (3734 expanded)
%              Number of equality atoms :   21 ( 230 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   72 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d38_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ~ ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X2)
                    & ~ ( v23_waybel_0(X3,X1,X2)
                      <=> ( v2_funct_1(X3)
                          & v5_orders_3(X3,X1,X2)
                          & ? [X4] :
                              ( v1_funct_1(X4)
                              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & X4 = k2_funct_1(X3)
                              & v5_orders_3(X4,X2,X1) ) ) ) )
                & ( ~ ( ~ v2_struct_0(X1)
                      & ~ v2_struct_0(X2) )
                 => ( v23_waybel_0(X3,X1,X2)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',d38_waybel_0)).

fof(t68_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_orders_2(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v23_waybel_0(X3,X1,X2)
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ( X4 = k2_funct_1(X3)
                     => v23_waybel_0(X4,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',t68_waybel_0)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',t65_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',cc1_relset_1)).

fof(t62_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t68_waybel_0.p',t62_funct_1)).

fof(c_0_5,plain,(
    ! [X1,X3,X2] :
      ( epred1_3(X2,X3,X1)
    <=> ( ~ ( ~ v2_struct_0(X1)
            & ~ v2_struct_0(X2)
            & ~ ( v23_waybel_0(X3,X1,X2)
              <=> ( v2_funct_1(X3)
                  & v5_orders_3(X3,X1,X2)
                  & ? [X4] :
                      ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & X4 = k2_funct_1(X3)
                      & v5_orders_3(X4,X2,X1) ) ) ) )
        & ( ~ ( ~ v2_struct_0(X1)
              & ~ v2_struct_0(X2) )
         => ( v23_waybel_0(X3,X1,X2)
          <=> ( v2_struct_0(X1)
              & v2_struct_0(X2) ) ) ) ) ) ),
    introduced(definition)).

fof(c_0_6,plain,(
    ! [X1,X3,X2] :
      ( epred1_3(X2,X3,X1)
     => ( ~ ( ~ v2_struct_0(X1)
            & ~ v2_struct_0(X2)
            & ~ ( v23_waybel_0(X3,X1,X2)
              <=> ( v2_funct_1(X3)
                  & v5_orders_3(X3,X1,X2)
                  & ? [X4] :
                      ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & X4 = k2_funct_1(X3)
                      & v5_orders_3(X4,X2,X1) ) ) ) )
        & ( ~ ( ~ v2_struct_0(X1)
              & ~ v2_struct_0(X2) )
         => ( v23_waybel_0(X3,X1,X2)
          <=> ( v2_struct_0(X1)
              & v2_struct_0(X2) ) ) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_5])).

fof(c_0_7,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => epred1_3(X2,X3,X1) ) ) ) ),
    inference(apply_def,[status(thm)],[d38_waybel_0,c_0_5])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_orders_2(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v23_waybel_0(X3,X1,X2)
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                     => ( X4 = k2_funct_1(X3)
                       => v23_waybel_0(X4,X2,X1) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_waybel_0])).

fof(c_0_9,plain,(
    ! [X46,X47,X48,X50] :
      ( ( v2_funct_1(X47)
        | ~ v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( v5_orders_3(X47,X46,X48)
        | ~ v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( v1_funct_1(esk9_3(X46,X47,X48))
        | ~ v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( v1_funct_2(esk9_3(X46,X47,X48),u1_struct_0(X48),u1_struct_0(X46))
        | ~ v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( m1_subset_1(esk9_3(X46,X47,X48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X46))))
        | ~ v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( esk9_3(X46,X47,X48) = k2_funct_1(X47)
        | ~ v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( v5_orders_3(esk9_3(X46,X47,X48),X48,X46)
        | ~ v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( ~ v2_funct_1(X47)
        | ~ v5_orders_3(X47,X46,X48)
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,u1_struct_0(X48),u1_struct_0(X46))
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X46))))
        | X50 != k2_funct_1(X47)
        | ~ v5_orders_3(X50,X48,X46)
        | v23_waybel_0(X47,X46,X48)
        | v2_struct_0(X46)
        | v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( v2_struct_0(X46)
        | ~ v23_waybel_0(X47,X46,X48)
        | ~ v2_struct_0(X46)
        | ~ epred1_3(X48,X47,X46) )
      & ( v2_struct_0(X48)
        | ~ v23_waybel_0(X47,X46,X48)
        | ~ v2_struct_0(X46)
        | ~ epred1_3(X48,X47,X46) )
      & ( ~ v2_struct_0(X46)
        | ~ v2_struct_0(X48)
        | v23_waybel_0(X47,X46,X48)
        | ~ v2_struct_0(X46)
        | ~ epred1_3(X48,X47,X46) )
      & ( v2_struct_0(X46)
        | ~ v23_waybel_0(X47,X46,X48)
        | ~ v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( v2_struct_0(X48)
        | ~ v23_waybel_0(X47,X46,X48)
        | ~ v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) )
      & ( ~ v2_struct_0(X46)
        | ~ v2_struct_0(X48)
        | v23_waybel_0(X47,X46,X48)
        | ~ v2_struct_0(X48)
        | ~ epred1_3(X48,X47,X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])])).

fof(c_0_10,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_orders_2(X16)
      | ~ l1_orders_2(X17)
      | ~ v1_funct_1(X18)
      | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | epred1_3(X17,X18,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v23_waybel_0(esk3_0,esk1_0,esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    & esk4_0 = k2_funct_1(esk3_0)
    & ~ v23_waybel_0(esk4_0,esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_12,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ v2_funct_1(X40)
      | k2_funct_1(k2_funct_1(X40)) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_14,plain,
    ( v5_orders_3(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X1,X2,X3)
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | ~ v23_waybel_0(X2,X3,X1)
    | ~ v2_struct_0(X3)
    | ~ epred1_3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( epred1_3(X2,X3,X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( esk9_3(X1,X2,X3) = k2_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X2,X1,X3)
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( esk4_0 = k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( v2_funct_1(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X1,X2,X3)
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
    ! [X39] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v2_funct_1(X39)
      | v2_funct_1(k2_funct_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_funct_1])])).

cnf(c_0_28,plain,
    ( v23_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_funct_1(X1)
    | ~ v5_orders_3(X1,X2,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | X4 != k2_funct_1(X1)
    | ~ v5_orders_3(X4,X3,X2)
    | ~ epred1_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( v5_orders_3(X1,X2,X3)
    | v2_struct_0(X3)
    | ~ epred1_3(X3,X1,X2)
    | ~ v23_waybel_0(X1,X2,X3) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( epred1_3(esk2_0,esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_33,negated_conjecture,
    ( v23_waybel_0(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,plain,
    ( v5_orders_3(esk9_3(X1,X2,X3),X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X2,X1,X3)
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( esk9_3(X1,X2,X3) = k2_funct_1(X2)
    | v2_struct_0(X3)
    | ~ epred1_3(X3,X2,X1)
    | ~ v23_waybel_0(X2,X1,X3) ),
    inference(csr,[status(thm)],[c_0_22,c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0
    | ~ v2_funct_1(esk3_0)
    | ~ v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19])])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_38,plain,
    ( v2_funct_1(X1)
    | v2_struct_0(X2)
    | ~ epred1_3(X2,X1,X3)
    | ~ v23_waybel_0(X1,X3,X2) ),
    inference(csr,[status(thm)],[c_0_26,c_0_15])).

cnf(c_0_39,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( v23_waybel_0(X1,esk2_0,esk1_0)
    | k2_funct_1(X1) != esk3_0
    | ~ epred1_3(esk1_0,X1,esk2_0)
    | ~ v5_orders_3(esk3_0,esk1_0,esk2_0)
    | ~ v5_orders_3(X1,esk2_0,esk1_0)
    | ~ v2_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_18]),c_0_19])]),c_0_29]),c_0_30])).

cnf(c_0_41,plain,
    ( v5_orders_3(esk3_0,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_29])).

cnf(c_0_42,plain,
    ( v5_orders_3(esk9_3(X1,X2,X3),X3,X1)
    | v2_struct_0(X3)
    | ~ epred1_3(X3,X2,X1)
    | ~ v23_waybel_0(X2,X1,X3) ),
    inference(csr,[status(thm)],[c_0_34,c_0_15])).

cnf(c_0_43,plain,
    ( esk9_3(esk1_0,esk3_0,esk2_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_24]),c_0_33])]),c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_45,plain,
    ( v2_funct_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_33])]),c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_24]),c_0_19])]),c_0_37])])).

cnf(c_0_50,negated_conjecture,
    ( v23_waybel_0(X1,esk2_0,esk1_0)
    | k2_funct_1(X1) != esk3_0
    | ~ epred1_3(esk1_0,X1,esk2_0)
    | ~ v5_orders_3(X1,esk2_0,esk1_0)
    | ~ v2_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_51,plain,
    ( v5_orders_3(esk4_0,esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_32]),c_0_33])]),c_0_29])).

cnf(c_0_52,negated_conjecture,
    ( k2_funct_1(esk4_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_53,negated_conjecture,
    ( epred1_3(esk1_0,esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_46]),c_0_47]),c_0_48]),c_0_21]),c_0_20])])).

cnf(c_0_54,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_45])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v23_waybel_0(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_54])]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
