%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT2049+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:10 EST 2020

% Result     : Theorem 8.61s
% Output     : CNFRefutation 8.61s
% Verified   : 
% Statistics : Number of formulae       :  151 (21052 expanded)
%              Number of clauses        :  108 (7127 expanded)
%              Number of leaves         :   22 (5047 expanded)
%              Depth                    :   26
%              Number of atoms          :  792 (187974 expanded)
%              Number of equality atoms :  147 (19386 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal clause size      :  110 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( r2_hidden(X4,k2_relset_1(u1_struct_0(k5_waybel_9(X1,X2,X3)),u1_struct_0(X1),u1_waybel_0(X1,k5_waybel_9(X1,X2,X3))))
                <=> ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X3,X5)
                      & X4 = k2_waybel_0(X1,X2,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow19)).

fof(dt_k4_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
        & l1_waybel_0(k4_waybel_9(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(redefinition_k5_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => k5_waybel_9(X1,X2,X3) = k4_waybel_9(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_waybel_9)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k5_waybel_9,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( v6_waybel_0(k5_waybel_9(X1,X2,X3),X1)
        & m2_yellow_6(k5_waybel_9(X1,X2,X3),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_9)).

fof(d7_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( ( v6_waybel_0(X4,X1)
                    & l1_waybel_0(X4,X1) )
                 => ( X4 = k4_waybel_9(X1,X2,X3)
                  <=> ( ! [X5] :
                          ( r2_hidden(X5,u1_struct_0(X4))
                        <=> ? [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                              & X6 = X5
                              & r1_orders_2(X2,X3,X6) ) )
                      & r2_relset_1(u1_struct_0(X4),u1_struct_0(X4),u1_orders_2(X4),k1_toler_1(u1_orders_2(X2),u1_struct_0(X4)))
                      & u1_waybel_0(X1,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(t16_waybel_9,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(k4_waybel_9(X1,X2,X3)))
                     => ( X4 = X5
                       => k2_waybel_0(X1,X2,X4) = k2_waybel_0(X1,k4_waybel_9(X1,X2,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_waybel_9)).

fof(dt_m2_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X2)
        & v4_orders_2(X2)
        & v7_waybel_0(X2)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m2_yellow_6(X3,X1,X2)
         => ( ~ v2_struct_0(X3)
            & v4_orders_2(X3)
            & v7_waybel_0(X3)
            & l1_waybel_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(d8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ! [X4] :
                    ( r2_hidden(X4,k2_relset_1(u1_struct_0(k5_waybel_9(X1,X2,X3)),u1_struct_0(X1),u1_waybel_0(X1,k5_waybel_9(X1,X2,X3))))
                  <=> ? [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                        & r1_orders_2(X2,X3,X5)
                        & X4 = k2_waybel_0(X1,X2,X5) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_yellow19])).

fof(c_0_23,plain,(
    ! [X39,X40,X41] :
      ( ( v6_waybel_0(k4_waybel_9(X39,X40,X41),X39)
        | v2_struct_0(X39)
        | ~ l1_struct_0(X39)
        | v2_struct_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) )
      & ( l1_waybel_0(k4_waybel_9(X39,X40,X41),X39)
        | v2_struct_0(X39)
        | ~ l1_struct_0(X39)
        | v2_struct_0(X40)
        | ~ l1_waybel_0(X40,X39)
        | ~ m1_subset_1(X41,u1_struct_0(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_waybel_9])])])])).

fof(c_0_24,negated_conjecture,(
    ! [X83] :
      ( ~ v2_struct_0(esk7_0)
      & l1_struct_0(esk7_0)
      & ~ v2_struct_0(esk8_0)
      & v4_orders_2(esk8_0)
      & v7_waybel_0(esk8_0)
      & l1_waybel_0(esk8_0,esk7_0)
      & m1_subset_1(esk9_0,u1_struct_0(esk8_0))
      & ( ~ r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0))))
        | ~ m1_subset_1(X83,u1_struct_0(esk8_0))
        | ~ r1_orders_2(esk8_0,esk9_0,X83)
        | esk10_0 != k2_waybel_0(esk7_0,esk8_0,X83) )
      & ( m1_subset_1(esk11_0,u1_struct_0(esk8_0))
        | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0)))) )
      & ( r1_orders_2(esk8_0,esk9_0,esk11_0)
        | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0)))) )
      & ( esk10_0 = k2_waybel_0(esk7_0,esk8_0,esk11_0)
        | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0)))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])])])).

fof(c_0_25,plain,(
    ! [X66,X67,X68] :
      ( v2_struct_0(X66)
      | ~ l1_struct_0(X66)
      | v2_struct_0(X67)
      | ~ v4_orders_2(X67)
      | ~ v7_waybel_0(X67)
      | ~ l1_waybel_0(X67,X66)
      | ~ m1_subset_1(X68,u1_struct_0(X67))
      | k5_waybel_9(X66,X67,X68) = k4_waybel_9(X66,X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k5_waybel_9])])])).

cnf(c_0_26,plain,
    ( l1_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( l1_waybel_0(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k5_waybel_9(X1,X2,X3) = k4_waybel_9(X1,X2,X3)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( v7_waybel_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v4_orders_2(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X51,X52] :
      ( ( v1_funct_1(u1_waybel_0(X51,X52))
        | ~ l1_struct_0(X51)
        | ~ l1_waybel_0(X52,X51) )
      & ( v1_funct_2(u1_waybel_0(X51,X52),u1_struct_0(X52),u1_struct_0(X51))
        | ~ l1_struct_0(X51)
        | ~ l1_waybel_0(X52,X51) )
      & ( m1_subset_1(u1_waybel_0(X51,X52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X51))))
        | ~ l1_struct_0(X51)
        | ~ l1_waybel_0(X52,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_35,negated_conjecture,
    ( l1_waybel_0(k4_waybel_9(esk7_0,esk8_0,X1),esk7_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( k5_waybel_9(esk7_0,esk8_0,X1) = k4_waybel_9(esk7_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_32]),c_0_33]),c_0_28])]),c_0_29]),c_0_30])).

fof(c_0_38,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | k2_relset_1(X59,X60,X61) = k2_relat_1(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( l1_waybel_0(k4_waybel_9(esk7_0,esk8_0,esk9_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_41,plain,(
    ! [X42,X43,X44] :
      ( ( v6_waybel_0(k5_waybel_9(X42,X43,X44),X42)
        | v2_struct_0(X42)
        | ~ l1_struct_0(X42)
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) )
      & ( m2_yellow_6(k5_waybel_9(X42,X43,X44),X42,X43)
        | v2_struct_0(X42)
        | ~ l1_struct_0(X42)
        | v2_struct_0(X43)
        | ~ v4_orders_2(X43)
        | ~ v7_waybel_0(X43)
        | ~ l1_waybel_0(X43,X42)
        | ~ m1_subset_1(X44,u1_struct_0(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_9])])])])).

fof(c_0_42,plain,(
    ! [X22,X23,X24,X25,X26,X28,X29,X31] :
      ( ( m1_subset_1(esk4_5(X22,X23,X24,X25,X26),u1_struct_0(X23))
        | ~ r2_hidden(X26,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( esk4_5(X22,X23,X24,X25,X26) = X26
        | ~ r2_hidden(X26,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r1_orders_2(X23,X24,esk4_5(X22,X23,X24,X25,X26))
        | ~ r2_hidden(X26,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( ~ m1_subset_1(X29,u1_struct_0(X23))
        | X29 != X28
        | ~ r1_orders_2(X23,X24,X29)
        | r2_hidden(X28,u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( u1_waybel_0(X22,X25) = k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 != k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( ~ r2_hidden(esk5_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ m1_subset_1(X31,u1_struct_0(X23))
        | X31 != esk5_4(X22,X23,X24,X25)
        | ~ r1_orders_2(X23,X24,X31)
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( m1_subset_1(esk6_4(X22,X23,X24,X25),u1_struct_0(X23))
        | r2_hidden(esk5_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( esk6_4(X22,X23,X24,X25) = esk5_4(X22,X23,X24,X25)
        | r2_hidden(esk5_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) )
      & ( r1_orders_2(X23,X24,esk6_4(X22,X23,X24,X25))
        | r2_hidden(esk5_4(X22,X23,X24,X25),u1_struct_0(X25))
        | ~ r2_relset_1(u1_struct_0(X25),u1_struct_0(X25),u1_orders_2(X25),k1_toler_1(u1_orders_2(X23),u1_struct_0(X25)))
        | u1_waybel_0(X22,X25) != k2_partfun1(u1_struct_0(X23),u1_struct_0(X22),u1_waybel_0(X22,X23),u1_struct_0(X25))
        | X25 = k4_waybel_9(X22,X23,X24)
        | ~ v6_waybel_0(X25,X22)
        | ~ l1_waybel_0(X25,X22)
        | ~ m1_subset_1(X24,u1_struct_0(X23))
        | v2_struct_0(X23)
        | ~ l1_waybel_0(X23,X22)
        | v2_struct_0(X22)
        | ~ l1_struct_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_waybel_9])])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk8_0,esk9_0,esk11_0)
    | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( k5_waybel_9(esk7_0,esk8_0,esk9_0) = k4_waybel_9(esk7_0,esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_45,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_28])])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk11_0,u1_struct_0(esk8_0))
    | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,plain,
    ( m2_yellow_6(k5_waybel_9(X1,X2,X3),X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v4_orders_2(X2)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,u1_struct_0(X5))
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X1 != X3
    | ~ r1_orders_2(X2,X4,X1)
    | X5 != k4_waybel_9(X6,X2,X4)
    | ~ v6_waybel_0(X5,X6)
    | ~ l1_waybel_0(X5,X6)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X6)
    | ~ l1_struct_0(X6) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( v6_waybel_0(k4_waybel_9(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk8_0,esk9_0,esk11_0)
    | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( k2_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))) = k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | m1_subset_1(esk11_0,u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_44]),c_0_44])).

fof(c_0_54,plain,(
    ! [X69,X70,X71,X72,X73] :
      ( v2_struct_0(X69)
      | ~ l1_struct_0(X69)
      | v2_struct_0(X70)
      | ~ v7_waybel_0(X70)
      | ~ l1_waybel_0(X70,X69)
      | ~ m1_subset_1(X71,u1_struct_0(X70))
      | ~ m1_subset_1(X72,u1_struct_0(X70))
      | ~ m1_subset_1(X73,u1_struct_0(k4_waybel_9(X69,X70,X71)))
      | X72 != X73
      | k2_waybel_0(X69,X70,X72) = k2_waybel_0(X69,k4_waybel_9(X69,X70,X71),X73) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t16_waybel_9])])])])).

fof(c_0_55,plain,(
    ! [X48,X49,X50] :
      ( ( ~ v2_struct_0(X50)
        | ~ m2_yellow_6(X50,X48,X49)
        | v2_struct_0(X48)
        | ~ l1_struct_0(X48)
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48) )
      & ( v4_orders_2(X50)
        | ~ m2_yellow_6(X50,X48,X49)
        | v2_struct_0(X48)
        | ~ l1_struct_0(X48)
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48) )
      & ( v7_waybel_0(X50)
        | ~ m2_yellow_6(X50,X48,X49)
        | v2_struct_0(X48)
        | ~ l1_struct_0(X48)
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48) )
      & ( l1_waybel_0(X50,X48)
        | ~ m2_yellow_6(X50,X48,X49)
        | v2_struct_0(X48)
        | ~ l1_struct_0(X48)
        | v2_struct_0(X49)
        | ~ v4_orders_2(X49)
        | ~ v7_waybel_0(X49)
        | ~ l1_waybel_0(X49,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_yellow_6])])])])])).

cnf(c_0_56,negated_conjecture,
    ( m2_yellow_6(k5_waybel_9(esk7_0,esk8_0,X1),esk7_0,esk8_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_27]),c_0_32]),c_0_33]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_hidden(X3,u1_struct_0(k4_waybel_9(X1,X2,X4)))
    | ~ r1_orders_2(X2,X4,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])]),c_0_26]),c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk8_0,esk9_0,esk11_0)
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | m1_subset_1(esk11_0,u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X4) = k2_waybel_0(X1,k4_waybel_9(X1,X2,X3),X5)
    | ~ l1_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X5,u1_struct_0(k4_waybel_9(X1,X2,X3)))
    | X4 != X5 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_61,plain,(
    ! [X33,X34,X35] :
      ( v2_struct_0(X33)
      | ~ l1_struct_0(X33)
      | v2_struct_0(X34)
      | ~ l1_waybel_0(X34,X33)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | k2_waybel_0(X33,X34,X35) = k3_funct_2(u1_struct_0(X34),u1_struct_0(X33),u1_waybel_0(X33,X34),X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).

cnf(c_0_62,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(X1)
    | ~ m2_yellow_6(X1,X2,X3)
    | ~ l1_struct_0(X2)
    | ~ v4_orders_2(X3)
    | ~ v7_waybel_0(X3)
    | ~ l1_waybel_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( m2_yellow_6(k4_waybel_9(esk7_0,esk8_0,esk9_0),esk7_0,esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_36]),c_0_44])).

fof(c_0_64,plain,(
    ! [X74,X75] :
      ( ~ r2_hidden(X74,X75)
      | m1_subset_1(X74,X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_65,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | r2_hidden(esk11_0,u1_struct_0(k4_waybel_9(X1,esk8_0,esk9_0)))
    | ~ l1_waybel_0(esk8_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_36])]),c_0_29]),c_0_59])).

fof(c_0_66,plain,(
    ! [X62,X63,X64,X65] :
      ( v1_xboole_0(X62)
      | ~ v1_funct_1(X64)
      | ~ v1_funct_2(X64,X62,X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63)))
      | ~ m1_subset_1(X65,X62)
      | k3_funct_2(X62,X63,X64,X65) = k1_funct_1(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_67,plain,
    ( v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_68,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_69,plain,(
    ! [X12,X13,X14,X16,X17,X18,X20] :
      ( ( r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X12))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,esk1_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk2_2(X12,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X12))
        | esk2_2(X12,X18) != k1_funct_1(X12,X20)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk3_2(X12,X18),k1_relat_1(X12))
        | r2_hidden(esk2_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk2_2(X12,X18) = k1_funct_1(X12,esk3_2(X12,X18))
        | r2_hidden(esk2_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_70,plain,(
    ! [X56,X57,X58] :
      ( ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
      | k1_relset_1(X56,X57,X58) = k1_relat_1(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_71,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | v1_relat_1(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_72,plain,(
    ! [X54,X55] : v1_relat_1(k2_zfmisc_1(X54,X55)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_73,plain,
    ( k2_waybel_0(X1,k4_waybel_9(X1,X2,X3),X4) = k2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v7_waybel_0(X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_32]),c_0_33]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | r2_hidden(esk11_0,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_27]),c_0_28])]),c_0_30])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_2(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_40]),c_0_28])])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_40]),c_0_28])])).

cnf(c_0_81,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_82,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_83,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_85,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_funct_2(X11,X9,X10)
        | X9 = k1_relset_1(X9,X10,X11)
        | X10 = k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( X9 != k1_relset_1(X9,X10,X11)
        | v1_funct_2(X11,X9,X10)
        | X10 = k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( ~ v1_funct_2(X11,X9,X10)
        | X9 = k1_relset_1(X9,X10,X11)
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( X9 != k1_relset_1(X9,X10,X11)
        | v1_funct_2(X11,X9,X10)
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( ~ v1_funct_2(X11,X9,X10)
        | X11 = k1_xboole_0
        | X9 = k1_xboole_0
        | X10 != k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( X11 != k1_xboole_0
        | v1_funct_2(X11,X9,X10)
        | X9 = k1_xboole_0
        | X10 != k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_86,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,X1),X2) = k2_waybel_0(esk7_0,esk8_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_27]),c_0_32]),c_0_28])]),c_0_30]),c_0_29])).

cnf(c_0_87,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),X1) = k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_40]),c_0_28])]),c_0_75]),c_0_30])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | m1_subset_1(esk11_0,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),X1) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),X1)
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | ~ m1_subset_1(X1,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_46])])).

cnf(c_0_90,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_81])])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))) = k1_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_46])).

cnf(c_0_92,negated_conjecture,
    ( v1_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_46]),c_0_84])])).

cnf(c_0_93,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( esk10_0 = k2_waybel_0(esk7_0,esk8_0,esk11_0)
    | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_95,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,X1),esk11_0) = k2_waybel_0(esk7_0,esk8_0,esk11_0)
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | ~ m1_subset_1(esk11_0,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_59])).

cnf(c_0_96,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk11_0) = k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk11_0)
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk11_0) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk11_0)
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),X1),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | ~ r2_hidden(X1,k1_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_80]),c_0_92])])).

cnf(c_0_99,negated_conjecture,
    ( k1_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))) = u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))
    | u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_79]),c_0_46])])).

cnf(c_0_100,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,esk11_0) = esk10_0
    | r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_44]),c_0_44])).

cnf(c_0_101,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk11_0) = k2_waybel_0(esk7_0,esk8_0,esk11_0)
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_36]),c_0_88])).

cnf(c_0_102,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk11_0) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk11_0)
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),X1),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | ~ r2_hidden(X1,u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,esk11_0) = esk10_0
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(rw,[status(thm)],[c_0_100,c_0_52])).

cnf(c_0_105,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,esk11_0) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk11_0)
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_106,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_107,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk11_0),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_77])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk11_0) = esk10_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_111,plain,
    ( m1_subset_1(esk4_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_112,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r2_hidden(esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0),k1_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_91]),c_0_80]),c_0_92])])).

cnf(c_0_113,plain,
    ( esk4_5(X1,X2,X3,X4,X5) = X5
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X1,X2,X3)
    | ~ v6_waybel_0(X4,X1)
    | ~ l1_waybel_0(X4,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_114,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk4_5(X2,X1,X3,k4_waybel_9(X2,X1,X3),X4),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X2,X1,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_111]),c_0_26]),c_0_50])).

cnf(c_0_115,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r2_hidden(esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0),u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_112,c_0_99])).

cnf(c_0_116,plain,
    ( esk4_5(X1,X2,X3,k4_waybel_9(X1,X2,X3),X4) = X4
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X1,X2,X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_113]),c_0_26]),c_0_50])).

cnf(c_0_117,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | m1_subset_1(esk4_5(esk7_0,esk8_0,esk9_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)),u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_27]),c_0_28]),c_0_36])]),c_0_30]),c_0_29])).

cnf(c_0_118,negated_conjecture,
    ( esk4_5(esk7_0,esk8_0,esk9_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_115]),c_0_27]),c_0_28]),c_0_36])]),c_0_30]),c_0_29])).

cnf(c_0_119,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_120,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | m1_subset_1(esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0),u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_115])).

cnf(c_0_121,plain,
    ( r1_orders_2(X1,X2,esk4_5(X3,X1,X2,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r2_hidden(X5,u1_struct_0(X4))
    | X4 != k4_waybel_9(X3,X1,X2)
    | ~ v6_waybel_0(X4,X3)
    | ~ l1_waybel_0(X4,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_122,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k5_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k5_waybel_9(esk7_0,esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0))
    | ~ r1_orders_2(esk8_0,esk9_0,X1)
    | esk10_0 != k2_waybel_0(esk7_0,esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_123,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,X1),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = k2_waybel_0(esk7_0,esk8_0,esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0))
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | ~ m1_subset_1(esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0),u1_struct_0(k4_waybel_9(esk7_0,esk8_0,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0))
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_87,c_0_120])).

cnf(c_0_125,negated_conjecture,
    ( k3_funct_2(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0))
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_120])).

cnf(c_0_126,plain,
    ( r1_orders_2(X1,X2,esk4_5(X3,X1,X2,k4_waybel_9(X3,X1,X2),X4))
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_struct_0(X3)
    | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X3,X1,X2)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_121]),c_0_26]),c_0_50])).

cnf(c_0_127,plain,
    ( X1 = k1_funct_1(X2,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_128,plain,(
    ! [X46,X47] :
      ( ~ l1_struct_0(X46)
      | ~ l1_waybel_0(X47,X46)
      | l1_orders_2(X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_129,negated_conjecture,
    ( esk10_0 != k2_waybel_0(esk7_0,esk8_0,X1)
    | ~ r1_orders_2(esk8_0,esk9_0,X1)
    | ~ r2_hidden(esk10_0,k2_relset_1(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)),u1_struct_0(esk7_0),u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_44]),c_0_44])).

cnf(c_0_130,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = k2_waybel_0(esk7_0,esk8_0,esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0))
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_36]),c_0_120])).

cnf(c_0_131,negated_conjecture,
    ( k2_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0))
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_132,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r1_orders_2(esk8_0,esk9_0,esk4_5(esk7_0,esk8_0,esk9_0,k4_waybel_9(esk7_0,esk8_0,esk9_0),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_115]),c_0_27]),c_0_28]),c_0_36])]),c_0_29]),c_0_30])).

cnf(c_0_133,plain,
    ( k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_127])).

fof(c_0_134,plain,(
    ! [X45] :
      ( ~ l1_orders_2(X45)
      | l1_struct_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_135,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_128])).

fof(c_0_136,plain,(
    ! [X53] :
      ( v2_struct_0(X53)
      | ~ l1_struct_0(X53)
      | ~ v1_xboole_0(u1_struct_0(X53)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_137,negated_conjecture,
    ( esk10_0 != k2_waybel_0(esk7_0,esk8_0,X1)
    | ~ r1_orders_2(esk8_0,esk9_0,X1)
    | ~ r2_hidden(esk10_0,k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))))
    | ~ m1_subset_1(X1,u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_129,c_0_52])).

cnf(c_0_138,negated_conjecture,
    ( k2_waybel_0(esk7_0,esk8_0,esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0))
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_139,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)))
    | r1_orders_2(esk8_0,esk9_0,esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_118])).

cnf(c_0_140,negated_conjecture,
    ( k1_funct_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),esk1_3(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0)),k2_relat_1(u1_waybel_0(esk7_0,k4_waybel_9(esk7_0,esk8_0,esk9_0))),esk10_0)) = esk10_0
    | u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_110]),c_0_80]),c_0_92])])).

cnf(c_0_141,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( l1_orders_2(k4_waybel_9(esk7_0,esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_40]),c_0_28])])).

cnf(c_0_143,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_136])).

cnf(c_0_144,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_119]),c_0_110]),c_0_139]),c_0_140])).

cnf(c_0_145,negated_conjecture,
    ( l1_struct_0(k4_waybel_9(esk7_0,esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_141,c_0_142])).

cnf(c_0_146,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_147,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_148,negated_conjecture,
    ( u1_struct_0(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_145])]),c_0_75])).

cnf(c_0_149,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_146,c_0_147])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_148]),c_0_149]),c_0_28])]),c_0_30]),
    [proof]).

%------------------------------------------------------------------------------
