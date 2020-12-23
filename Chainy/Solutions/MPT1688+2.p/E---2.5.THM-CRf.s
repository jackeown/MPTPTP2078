%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1688+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:07 EST 2020

% Result     : Theorem 51.00s
% Output     : CNFRefutation 51.00s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 517 expanded)
%              Number of clauses        :   40 ( 161 expanded)
%              Number of leaves         :    6 ( 128 expanded)
%              Depth                    :    7
%              Number of atoms          :  309 (5837 expanded)
%              Number of equality atoms :   18 ( 365 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   72 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d38_waybel_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',cc1_relset_1)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t65_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',fc6_funct_1)).

fof(c_0_5,plain,(
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

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_5])).

fof(c_0_8,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => epred12_3(X2,X3,X1) ) ) ) ),
    inference(apply_def,[status(thm)],[d38_waybel_0,c_0_5])).

fof(c_0_9,plain,(
    ! [X3615,X3616,X3617] :
      ( ~ m1_subset_1(X3617,k1_zfmisc_1(k2_zfmisc_1(X3615,X3616)))
      | v1_relat_1(X3617) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1226_0)
    & l1_orders_2(esk1226_0)
    & ~ v2_struct_0(esk1227_0)
    & l1_orders_2(esk1227_0)
    & v1_funct_1(esk1228_0)
    & v1_funct_2(esk1228_0,u1_struct_0(esk1226_0),u1_struct_0(esk1227_0))
    & m1_subset_1(esk1228_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1226_0),u1_struct_0(esk1227_0))))
    & v23_waybel_0(esk1228_0,esk1226_0,esk1227_0)
    & v1_funct_1(esk1229_0)
    & v1_funct_2(esk1229_0,u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))
    & m1_subset_1(esk1229_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0))))
    & esk1229_0 = k2_funct_1(esk1228_0)
    & ~ v23_waybel_0(esk1229_0,esk1227_0,esk1226_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_11,plain,(
    ! [X10588,X10589,X10590,X10592] :
      ( ( v2_funct_1(X10589)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v5_orders_3(X10589,X10588,X10590)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v1_funct_1(esk1256_3(X10588,X10589,X10590))
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v1_funct_2(esk1256_3(X10588,X10589,X10590),u1_struct_0(X10590),u1_struct_0(X10588))
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( m1_subset_1(esk1256_3(X10588,X10589,X10590),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10590),u1_struct_0(X10588))))
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( esk1256_3(X10588,X10589,X10590) = k2_funct_1(X10589)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v5_orders_3(esk1256_3(X10588,X10589,X10590),X10590,X10588)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( ~ v2_funct_1(X10589)
        | ~ v5_orders_3(X10589,X10588,X10590)
        | ~ v1_funct_1(X10592)
        | ~ v1_funct_2(X10592,u1_struct_0(X10590),u1_struct_0(X10588))
        | ~ m1_subset_1(X10592,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10590),u1_struct_0(X10588))))
        | X10592 != k2_funct_1(X10589)
        | ~ v5_orders_3(X10592,X10590,X10588)
        | v23_waybel_0(X10589,X10588,X10590)
        | v2_struct_0(X10588)
        | v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v2_struct_0(X10588)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | ~ v2_struct_0(X10588)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v2_struct_0(X10590)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | ~ v2_struct_0(X10588)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( ~ v2_struct_0(X10588)
        | ~ v2_struct_0(X10590)
        | v23_waybel_0(X10589,X10588,X10590)
        | ~ v2_struct_0(X10588)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v2_struct_0(X10588)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | ~ v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( v2_struct_0(X10590)
        | ~ v23_waybel_0(X10589,X10588,X10590)
        | ~ v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) )
      & ( ~ v2_struct_0(X10588)
        | ~ v2_struct_0(X10590)
        | v23_waybel_0(X10589,X10588,X10590)
        | ~ v2_struct_0(X10590)
        | ~ epred12_3(X10590,X10589,X10588) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])])).

fof(c_0_12,plain,(
    ! [X10065,X10066,X10067] :
      ( ~ l1_orders_2(X10065)
      | ~ l1_orders_2(X10066)
      | ~ v1_funct_1(X10067)
      | ~ v1_funct_2(X10067,u1_struct_0(X10065),u1_struct_0(X10066))
      | ~ m1_subset_1(X10067,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10065),u1_struct_0(X10066))))
      | epred12_3(X10066,X10067,X10065) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_13,plain,(
    ! [X3107] :
      ( ~ v1_relat_1(X3107)
      | ~ v1_funct_1(X3107)
      | ~ v2_funct_1(X3107)
      | k2_funct_1(k2_funct_1(X3107)) = X3107 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_14,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1228_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1226_0),u1_struct_0(esk1227_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v2_funct_1(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X1,X2,X3)
    | ~ epred12_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | ~ v23_waybel_0(X2,X3,X1)
    | ~ v2_struct_0(X3)
    | ~ epred12_3(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( epred12_3(X2,X3,X1)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk1228_0,u1_struct_0(esk1226_0),u1_struct_0(esk1227_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk1227_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1226_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk1228_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( esk1256_3(X1,X2,X3) = k2_funct_1(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X2,X1,X3)
    | ~ epred12_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_24,plain,(
    ! [X2808] :
      ( ( v1_relat_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) )
      & ( v1_funct_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) )
      & ( v2_funct_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_25,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( esk1229_0 = k2_funct_1(esk1228_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk1228_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | v2_funct_1(X2)
    | ~ epred12_3(X1,X2,X3)
    | ~ v23_waybel_0(X2,X3,X1) ),
    inference(csr,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( epred12_3(esk1227_0,esk1228_0,esk1226_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( v23_waybel_0(esk1228_0,esk1226_0,esk1227_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk1227_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( v5_orders_3(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X1,X2,X3)
    | ~ epred12_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( v5_orders_3(esk1256_3(X1,X2,X3),X3,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v23_waybel_0(X2,X1,X3)
    | ~ epred12_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,plain,
    ( esk1256_3(X1,X2,X3) = k2_funct_1(X2)
    | v2_struct_0(X3)
    | ~ epred12_3(X3,X2,X1)
    | ~ v23_waybel_0(X2,X1,X3) ),
    inference(csr,[status(thm)],[c_0_23,c_0_17])).

cnf(c_0_35,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
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
    | ~ epred12_3(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk1229_0,u1_struct_0(esk1227_0),u1_struct_0(esk1226_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk1229_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk1229_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1227_0),u1_struct_0(esk1226_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( k2_funct_1(esk1229_0) = esk1228_0
    | ~ v2_funct_1(esk1228_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_26]),c_0_27])])).

cnf(c_0_41,plain,
    ( v2_funct_1(esk1228_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_42,plain,
    ( v5_orders_3(X1,X2,X3)
    | v2_struct_0(X3)
    | ~ epred12_3(X3,X1,X2)
    | ~ v23_waybel_0(X1,X2,X3) ),
    inference(csr,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_43,plain,
    ( v5_orders_3(esk1256_3(X1,X2,X3),X3,X1)
    | v2_struct_0(X3)
    | ~ epred12_3(X3,X2,X1)
    | ~ v23_waybel_0(X2,X1,X3) ),
    inference(csr,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( esk1256_3(esk1226_0,esk1228_0,esk1227_0) = esk1229_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_29]),c_0_26]),c_0_30])]),c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( v2_funct_1(esk1229_0)
    | ~ v2_funct_1(esk1228_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_22]),c_0_26]),c_0_27])])).

cnf(c_0_46,plain,
    ( v23_waybel_0(X1,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ epred12_3(X3,X1,X2)
    | ~ v5_orders_3(k2_funct_1(X1),X3,X2)
    | ~ v5_orders_3(X1,X2,X3)
    | ~ v1_funct_2(k2_funct_1(X1),u1_struct_0(X3),u1_struct_0(X2))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( epred12_3(esk1226_0,esk1229_0,esk1227_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_37]),c_0_21]),c_0_20]),c_0_38]),c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( k2_funct_1(esk1229_0) = esk1228_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_49,plain,
    ( v5_orders_3(esk1228_0,esk1226_0,esk1227_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( v5_orders_3(esk1229_0,esk1227_0,esk1226_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_29]),c_0_44]),c_0_30])]),c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( v2_funct_1(esk1229_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_41])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v23_waybel_0(esk1229_0,esk1227_0,esk1226_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk1226_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49]),c_0_50]),c_0_48]),c_0_19]),c_0_51]),c_0_48]),c_0_22]),c_0_48]),c_0_15])]),c_0_52]),c_0_31]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
