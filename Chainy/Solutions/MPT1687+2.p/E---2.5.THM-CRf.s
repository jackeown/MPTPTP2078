%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1687+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 19.74s
% Output     : CNFRefutation 19.74s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 304 expanded)
%              Number of clauses        :   50 ( 104 expanded)
%              Number of leaves         :   14 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  371 (2907 expanded)
%              Number of equality atoms :   35 ( 199 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   72 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_waybel_0,conjecture,(
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
               => ( v1_funct_1(k2_funct_1(X3))
                  & v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & k2_relat_1(k2_funct_1(X3)) = u1_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT017+2.ax',dt_l1_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',fc2_struct_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',cc1_relset_1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT014+2.ax',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d38_waybel_0)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT008+2.ax',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT008+2.ax',t55_funct_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT014+2.ax',d4_partfun1)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',redefinition_k3_relset_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT008+2.ax',d9_funct_1)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT011+2.ax',dt_k3_relset_1)).

fof(c_0_13,negated_conjecture,(
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
                 => ( v1_funct_1(k2_funct_1(X3))
                    & v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & k2_relat_1(k2_funct_1(X3)) = u1_struct_0(X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_waybel_0])).

fof(c_0_14,plain,(
    ! [X6188] :
      ( ~ l1_orders_2(X6188)
      | l1_struct_0(X6188) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1226_0)
    & l1_orders_2(esk1226_0)
    & ~ v2_struct_0(esk1227_0)
    & l1_orders_2(esk1227_0)
    & v1_funct_1(esk1228_0)
    & v1_funct_2(esk1228_0,u1_struct_0(esk1226_0),u1_struct_0(esk1227_0))
    & m1_subset_1(esk1228_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1226_0),u1_struct_0(esk1227_0))))
    & v23_waybel_0(esk1228_0,esk1226_0,esk1227_0)
    & ( ~ v1_funct_1(k2_funct_1(esk1228_0))
      | ~ v1_funct_2(k2_funct_1(esk1228_0),u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))
      | ~ m1_subset_1(k2_funct_1(esk1228_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))))
      | k2_relat_1(k2_funct_1(esk1228_0)) != u1_struct_0(esk1226_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X5932] :
      ( v2_struct_0(X5932)
      | ~ l1_struct_0(X5932)
      | ~ v1_xboole_0(u1_struct_0(X5932)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_17,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_orders_2(esk1227_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X1,X3,X2] :
      ( epred12_3(X2,X3,X1)
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

fof(c_0_20,plain,(
    ! [X3615,X3616,X3617] :
      ( ~ m1_subset_1(X3617,k1_zfmisc_1(k2_zfmisc_1(X3615,X3616)))
      | v1_relat_1(X3617) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X4814,X4815,X4816] :
      ( ( v1_funct_1(X4816)
        | ~ v1_funct_1(X4816)
        | ~ v1_funct_2(X4816,X4814,X4815)
        | ~ m1_subset_1(X4816,k1_zfmisc_1(k2_zfmisc_1(X4814,X4815)))
        | v1_xboole_0(X4815) )
      & ( v1_partfun1(X4816,X4814)
        | ~ v1_funct_1(X4816)
        | ~ v1_funct_2(X4816,X4814,X4815)
        | ~ m1_subset_1(X4816,k1_zfmisc_1(k2_zfmisc_1(X4814,X4815)))
        | v1_xboole_0(X4815) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_struct_0(esk1227_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1227_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X3618,X3619,X3620] :
      ( ( v4_relat_1(X3620,X3618)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) )
      & ( v5_relat_1(X3620,X3619)
        | ~ m1_subset_1(X3620,k1_zfmisc_1(k2_zfmisc_1(X3618,X3619))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_26,plain,(
    ! [X1,X3,X2] :
      ( epred12_3(X2,X3,X1)
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
    inference(split_equiv,[status(thm)],[c_0_19])).

fof(c_0_27,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => epred12_3(X2,X3,X1) ) ) ) ),
    inference(apply_def,[status(thm)],[d38_waybel_0,c_0_19])).

fof(c_0_28,plain,(
    ! [X2785] :
      ( ( v1_relat_1(k2_funct_1(X2785))
        | ~ v1_relat_1(X2785)
        | ~ v1_funct_1(X2785) )
      & ( v1_funct_1(k2_funct_1(X2785))
        | ~ v1_relat_1(X2785)
        | ~ v1_funct_1(X2785) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_29,plain,(
    ! [X3090] :
      ( ( k2_relat_1(X3090) = k1_relat_1(k2_funct_1(X3090))
        | ~ v2_funct_1(X3090)
        | ~ v1_relat_1(X3090)
        | ~ v1_funct_1(X3090) )
      & ( k1_relat_1(X3090) = k2_relat_1(k2_funct_1(X3090))
        | ~ v2_funct_1(X3090)
        | ~ v1_relat_1(X3090)
        | ~ v1_funct_1(X3090) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk1228_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1226_0),u1_struct_0(esk1227_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_32,plain,(
    ! [X4881,X4882] :
      ( ( ~ v1_partfun1(X4882,X4881)
        | k1_relat_1(X4882) = X4881
        | ~ v1_relat_1(X4882)
        | ~ v4_relat_1(X4882,X4881) )
      & ( k1_relat_1(X4882) != X4881
        | v1_partfun1(X4882,X4881)
        | ~ v1_relat_1(X4882)
        | ~ v4_relat_1(X4882,X4881) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_33,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk1228_0,u1_struct_0(esk1226_0),u1_struct_0(esk1227_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk1228_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1227_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_37,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X10584,X10585,X10586,X10588] :
      ( ( v2_funct_1(X10585)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v5_orders_3(X10585,X10584,X10586)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v1_funct_1(esk1255_3(X10584,X10585,X10586))
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v1_funct_2(esk1255_3(X10584,X10585,X10586),u1_struct_0(X10586),u1_struct_0(X10584))
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( m1_subset_1(esk1255_3(X10584,X10585,X10586),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10586),u1_struct_0(X10584))))
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( esk1255_3(X10584,X10585,X10586) = k2_funct_1(X10585)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v5_orders_3(esk1255_3(X10584,X10585,X10586),X10586,X10584)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( ~ v2_funct_1(X10585)
        | ~ v5_orders_3(X10585,X10584,X10586)
        | ~ v1_funct_1(X10588)
        | ~ v1_funct_2(X10588,u1_struct_0(X10586),u1_struct_0(X10584))
        | ~ m1_subset_1(X10588,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10586),u1_struct_0(X10584))))
        | X10588 != k2_funct_1(X10585)
        | ~ v5_orders_3(X10588,X10586,X10584)
        | v23_waybel_0(X10585,X10584,X10586)
        | v2_struct_0(X10584)
        | v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v2_struct_0(X10584)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | ~ v2_struct_0(X10584)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v2_struct_0(X10586)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | ~ v2_struct_0(X10584)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( ~ v2_struct_0(X10584)
        | ~ v2_struct_0(X10586)
        | v23_waybel_0(X10585,X10584,X10586)
        | ~ v2_struct_0(X10584)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v2_struct_0(X10584)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | ~ v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( v2_struct_0(X10586)
        | ~ v23_waybel_0(X10585,X10584,X10586)
        | ~ v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) )
      & ( ~ v2_struct_0(X10584)
        | ~ v2_struct_0(X10586)
        | v23_waybel_0(X10585,X10584,X10586)
        | ~ v2_struct_0(X10586)
        | ~ epred12_3(X10586,X10585,X10584) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_26])])])])])])).

fof(c_0_39,plain,(
    ! [X10065,X10066,X10067] :
      ( ~ l1_orders_2(X10065)
      | ~ l1_orders_2(X10066)
      | ~ v1_funct_1(X10067)
      | ~ v1_funct_2(X10067,u1_struct_0(X10065),u1_struct_0(X10066))
      | ~ m1_subset_1(X10067,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10065),u1_struct_0(X10066))))
      | epred12_3(X10066,X10067,X10065) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_40,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk1228_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_43,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v1_partfun1(esk1228_0,u1_struct_0(esk1226_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_31])]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v4_relat_1(esk1228_0,u1_struct_0(esk1226_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_46,plain,
    ( v2_funct_1(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X1,X2,X3)
    | ~ epred12_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | ~ v23_waybel_0(X2,X3,X1)
    | ~ v2_struct_0(X3)
    | ~ epred12_3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( epred12_3(X2,X3,X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( l1_orders_2(esk1226_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_50,plain,(
    ! [X3685,X3686,X3687] :
      ( ~ m1_subset_1(X3687,k1_zfmisc_1(k2_zfmisc_1(X3685,X3686)))
      | k3_relset_1(X3685,X3686,X3687) = k4_relat_1(X3687) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

fof(c_0_51,plain,(
    ! [X2784] :
      ( ~ v1_relat_1(X2784)
      | ~ v1_funct_1(X2784)
      | ~ v2_funct_1(X2784)
      | k2_funct_1(X2784) = k4_relat_1(X2784) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk1228_0))
    | ~ v1_relat_1(esk1228_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1228_0)) = k1_relat_1(esk1228_0)
    | ~ v2_funct_1(esk1228_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_42])])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk1228_0) = u1_struct_0(esk1226_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_42])])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_funct_1(X2)
    | ~ epred12_3(X1,X2,X3)
    | ~ v23_waybel_0(X2,X3,X1) ),
    inference(csr,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( epred12_3(esk1227_0,esk1228_0,esk1226_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_34]),c_0_18]),c_0_49]),c_0_35]),c_0_31])])).

cnf(c_0_57,negated_conjecture,
    ( v23_waybel_0(esk1228_0,esk1226_0,esk1227_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_58,plain,(
    ! [X3641,X3642,X3643] :
      ( ~ m1_subset_1(X3643,k1_zfmisc_1(k2_zfmisc_1(X3641,X3642)))
      | m1_subset_1(k3_relset_1(X3641,X3642,X3643),k1_zfmisc_1(k2_zfmisc_1(X3642,X3641))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_59,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk1228_0))
    | ~ v1_funct_2(k2_funct_1(esk1228_0),u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))
    | ~ m1_subset_1(k2_funct_1(esk1228_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))))
    | k2_relat_1(k2_funct_1(esk1228_0)) != u1_struct_0(esk1226_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk1228_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_42])])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1228_0)) = u1_struct_0(esk1226_0)
    | ~ v2_funct_1(esk1228_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,plain,
    ( v2_funct_1(esk1228_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])]),c_0_24])).

cnf(c_0_65,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k3_relset_1(u1_struct_0(esk1226_0),u1_struct_0(esk1227_0),esk1228_0) = k4_relat_1(esk1228_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( k4_relat_1(esk1228_0) = k2_funct_1(esk1228_0)
    | ~ v2_funct_1(esk1228_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_35]),c_0_42])])).

cnf(c_0_68,plain,
    ( esk1255_3(X1,X2,X3) = k2_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X2,X1,X3)
    | ~ epred12_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1228_0)) != u1_struct_0(esk1226_0)
    | ~ v1_funct_2(k2_funct_1(esk1228_0),u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))
    | ~ m1_subset_1(k2_funct_1(esk1228_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_70,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk1228_0)) = u1_struct_0(esk1226_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k4_relat_1(esk1228_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_31]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k4_relat_1(esk1228_0) = k2_funct_1(esk1228_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_64])])).

cnf(c_0_73,plain,
    ( v1_funct_2(esk1255_3(X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X2,X1,X3)
    | ~ epred12_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_74,plain,
    ( esk1255_3(X1,X2,X3) = k2_funct_1(X2)
    | v2_struct_0(X3)
    | ~ epred12_3(X3,X2,X1)
    | ~ v23_waybel_0(X2,X1,X3) ),
    inference(csr,[status(thm)],[c_0_68,c_0_47])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk1228_0),u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))
    | ~ m1_subset_1(k2_funct_1(esk1228_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk1228_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0)))) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v1_funct_2(esk1255_3(X2,X3,X1),u1_struct_0(X1),u1_struct_0(X2))
    | ~ epred12_3(X1,X3,X2)
    | ~ v23_waybel_0(X3,X2,X1) ),
    inference(csr,[status(thm)],[c_0_73,c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( esk1255_3(esk1226_0,esk1228_0,esk1227_0) = k2_funct_1(esk1228_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_56]),c_0_57])]),c_0_24])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk1228_0),u1_struct_0(esk1227_0),u1_struct_0(esk1226_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_56]),c_0_78]),c_0_57])]),c_0_24]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
