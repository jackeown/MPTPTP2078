%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:30 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  94 expanded)
%              Number of clauses        :   29 (  32 expanded)
%              Number of leaves         :    9 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  196 ( 679 expanded)
%              Number of equality atoms :   24 (  72 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ( v1_funct_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | v1_xboole_0(X12) )
      & ( v1_partfun1(X13,X11)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | v1_xboole_0(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v23_waybel_0(esk3_0,esk1_0,esk2_0)
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
      | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X19] :
      ( v2_struct_0(X19)
      | ~ l1_struct_0(X19)
      | ~ v1_xboole_0(u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_13,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

fof(c_0_17,plain,(
    ! [X8,X9,X10] :
      ( ( v4_relat_1(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( v5_relat_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ( ~ v1_partfun1(X15,X14)
        | k1_relat_1(X15) = X14
        | ~ v1_relat_1(X15)
        | ~ v4_relat_1(X15,X14) )
      & ( k1_relat_1(X15) != X14
        | v1_partfun1(X15,X14)
        | ~ v1_relat_1(X15)
        | ~ v4_relat_1(X15,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v1_partfun1(esk3_0,u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_23,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_25,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( v1_partfun1(esk3_0,u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_14]),
    [final]).

fof(c_0_29,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_30,plain,(
    ! [X16,X17,X18] :
      ( ( v1_funct_1(k2_funct_1(X18))
        | ~ v2_funct_1(X18)
        | k2_relset_1(X16,X17,X18) != X17
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v1_funct_2(k2_funct_1(X18),X17,X16)
        | ~ v2_funct_1(X18)
        | k2_relset_1(X16,X17,X18) != X17
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( m1_subset_1(k2_funct_1(X18),k1_zfmisc_1(k2_zfmisc_1(X17,X16)))
        | ~ v2_funct_1(X18)
        | k2_relset_1(X16,X17,X18) != X17
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

fof(c_0_31,plain,(
    ! [X4] :
      ( ( k2_relat_1(X4) = k1_relat_1(k2_funct_1(X4))
        | ~ v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) )
      & ( k1_relat_1(X4) = k2_relat_1(k2_funct_1(X4))
        | ~ v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_33,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_35,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_36,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_37,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_39,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_40,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_41,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( v5_relat_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_14]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( v23_waybel_0(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.14/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  
% 0.14/0.37  # No proof found!
% 0.14/0.37  # SZS status CounterSatisfiable
% 0.14/0.37  # SZS output start Saturation
% 0.14/0.37  fof(t67_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_waybel_0)).
% 0.14/0.37  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.14/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.37  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.14/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.37  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.14/0.37  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.14/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t67_waybel_0])).
% 0.14/0.37  fof(c_0_10, plain, ![X11, X12, X13]:((v1_funct_1(X13)|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_xboole_0(X12))&(v1_partfun1(X13,X11)|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_xboole_0(X12))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.14/0.37  fof(c_0_11, negated_conjecture, ((~v2_struct_0(esk1_0)&l1_orders_2(esk1_0))&((~v2_struct_0(esk2_0)&l1_orders_2(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v23_waybel_0(esk3_0,esk1_0,esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.14/0.37  fof(c_0_12, plain, ![X19]:(v2_struct_0(X19)|~l1_struct_0(X19)|~v1_xboole_0(u1_struct_0(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.37  cnf(c_0_13, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_15, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  fof(c_0_17, plain, ![X8, X9, X10]:((v4_relat_1(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))))&(v5_relat_1(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.37  fof(c_0_18, plain, ![X5, X6, X7]:(~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))|v1_relat_1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.37  fof(c_0_19, plain, ![X14, X15]:((~v1_partfun1(X15,X14)|k1_relat_1(X15)=X14|(~v1_relat_1(X15)|~v4_relat_1(X15,X14)))&(k1_relat_1(X15)!=X14|v1_partfun1(X15,X14)|(~v1_relat_1(X15)|~v4_relat_1(X15,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.14/0.37  cnf(c_0_20, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (v1_partfun1(esk3_0,u1_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])]), ['final']).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_23, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.37  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.14/0.37  cnf(c_0_25, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (v1_partfun1(esk3_0,u1_struct_0(esk1_0))|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), ['final']).
% 0.14/0.37  cnf(c_0_27, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_23, c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_24, c_0_14]), ['final']).
% 0.14/0.37  fof(c_0_29, plain, ![X20]:(~l1_orders_2(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.37  fof(c_0_30, plain, ![X16, X17, X18]:(((v1_funct_1(k2_funct_1(X18))|(~v2_funct_1(X18)|k2_relset_1(X16,X17,X18)!=X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&(v1_funct_2(k2_funct_1(X18),X17,X16)|(~v2_funct_1(X18)|k2_relset_1(X16,X17,X18)!=X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))))&(m1_subset_1(k2_funct_1(X18),k1_zfmisc_1(k2_zfmisc_1(X17,X16)))|(~v2_funct_1(X18)|k2_relset_1(X16,X17,X18)!=X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.14/0.37  fof(c_0_31, plain, ![X4]:((k2_relat_1(X4)=k1_relat_1(k2_funct_1(X4))|~v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4)))&(k1_relat_1(X4)=k2_relat_1(k2_funct_1(X4))|~v2_funct_1(X4)|(~v1_relat_1(X4)|~v1_funct_1(X4)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.14/0.37  cnf(c_0_33, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_35, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.14/0.37  cnf(c_0_36, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.14/0.37  cnf(c_0_37, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.14/0.37  cnf(c_0_38, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.14/0.37  cnf(c_0_39, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19]), ['final']).
% 0.14/0.37  cnf(c_0_40, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.14/0.37  cnf(c_0_41, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])]), ['final']).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, (v5_relat_1(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_14]), ['final']).
% 0.14/0.37  cnf(c_0_46, negated_conjecture, (v23_waybel_0(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.37  # SZS output end Saturation
% 0.14/0.37  # Proof object total steps             : 48
% 0.14/0.37  # Proof object clause steps            : 29
% 0.14/0.37  # Proof object formula steps           : 19
% 0.14/0.37  # Proof object conjectures             : 19
% 0.14/0.37  # Proof object clause conjectures      : 16
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 22
% 0.14/0.37  # Proof object initial formulas used   : 9
% 0.14/0.37  # Proof object generating inferences   : 7
% 0.14/0.37  # Proof object simplifying inferences  : 9
% 0.14/0.37  # Parsed axioms                        : 9
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 23
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 22
% 0.14/0.37  # Processed clauses                    : 29
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 29
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 0
% 0.14/0.37  # Backward-rewritten                   : 1
% 0.14/0.37  # Generated clauses                    : 8
% 0.14/0.37  # ...of the previous two non-trivial   : 7
% 0.14/0.37  # Contextual simplify-reflections      : 0
% 0.14/0.37  # Paramodulations                      : 8
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 0
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 28
% 0.14/0.37  #    Positive orientable unit clauses  : 10
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 2
% 0.14/0.37  #    Non-unit-clauses                  : 16
% 0.14/0.37  # Current number of unprocessed clauses: 0
% 0.14/0.37  # ...number of literals in the above   : 0
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 1
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 90
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 20
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.37  # Unit Clause-clause subsumption calls : 0
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 1
% 0.14/0.37  # BW rewrite match successes           : 1
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 1895
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.028 s
% 0.14/0.37  # System time              : 0.005 s
% 0.14/0.37  # Total time               : 0.033 s
% 0.14/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
