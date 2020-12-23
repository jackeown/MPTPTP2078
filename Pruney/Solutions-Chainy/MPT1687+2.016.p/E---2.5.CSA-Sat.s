%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:31 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 270 expanded)
%              Number of clauses        :   61 ( 111 expanded)
%              Number of leaves         :   12 (  73 expanded)
%              Depth                    :    6
%              Number of atoms          :  302 (1391 expanded)
%              Number of equality atoms :   81 ( 356 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(rc1_relset_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_xboole_0(X3)
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X20 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X20 != k1_xboole_0
        | v1_funct_2(X20,X18,X19)
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_relset_1(X15,X16,X17) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( m1_subset_1(esk1_2(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      & v1_xboole_0(esk1_2(X21,X22))
      & v1_relat_1(esk1_2(X21,X22))
      & v4_relat_1(esk1_2(X21,X22),X21)
      & v5_relat_1(esk1_2(X21,X22),X22) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).

fof(c_0_16,plain,(
    ! [X4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_17,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v23_waybel_0(esk4_0,esk2_0,esk3_0)
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      | k2_relat_1(k2_funct_1(esk4_0)) != u1_struct_0(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_19,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

fof(c_0_23,plain,(
    ! [X8] :
      ( ( k2_relat_1(X8) = k1_relat_1(k2_funct_1(X8))
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( k1_relat_1(X8) = k2_relat_1(k2_funct_1(X8))
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

fof(c_0_26,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_xboole_0(X12)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_27,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_28,plain,
    ( k1_relset_1(X1,X2,esk1_2(X1,X2)) = k1_relat_1(esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_29,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_30,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | k2_relat_1(k2_funct_1(esk4_0)) != u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_32,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]),
    [final]).

cnf(c_0_35,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_25]),
    [final]).

fof(c_0_38,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | m1_subset_1(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26]),
    [final]).

cnf(c_0_40,plain,
    ( v1_funct_2(esk1_2(k1_xboole_0,X1),k1_xboole_0,X1)
    | k1_relat_1(esk1_2(k1_xboole_0,X1)) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_21])]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk1_2(X2,X1),X2,X1)
    | k1_relat_1(esk1_2(X2,X1)) != X2 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_21])]),
    [final]).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22])])]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk4_0) != u1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(esk4_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_36])]),c_0_37]),
    [final]).

cnf(c_0_45,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_30]),c_0_22])]),
    [final]).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38]),
    [final]).

fof(c_0_47,plain,(
    ! [X24,X25,X26] :
      ( ( v1_funct_1(k2_funct_1(X26))
        | ~ v2_funct_1(X26)
        | k2_relset_1(X24,X25,X26) != X25
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( v1_funct_2(k2_funct_1(X26),X25,X24)
        | ~ v2_funct_1(X26)
        | k2_relset_1(X24,X25,X26) != X25
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) )
      & ( m1_subset_1(k2_funct_1(X26),k1_zfmisc_1(k2_zfmisc_1(X25,X24)))
        | ~ v2_funct_1(X26)
        | k2_relset_1(X24,X25,X26) != X25
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X24,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_48,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_51,plain,(
    ! [X27] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ v1_xboole_0(u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_52,plain,(
    ! [X28] :
      ( ~ l1_orders_2(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_22])).

cnf(c_0_54,plain,
    ( v1_xboole_0(esk1_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_55,plain,
    ( v1_funct_2(esk1_2(k1_xboole_0,X1),k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,esk1_2(k1_xboole_0,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_28]),
    [final]).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk1_2(X2,X1),X2,X1)
    | k1_relset_1(X2,X1,esk1_2(X2,X1)) != X2 ),
    inference(spm,[status(thm)],[c_0_41,c_0_28]),
    [final]).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_relset_1(X2,X3,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(esk4_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44]),
    [final]).

cnf(c_0_59,plain,
    ( k1_relset_1(X1,X2,esk1_2(X1,X2)) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(esk1_2(X1,X2),X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21]),
    [final]).

cnf(c_0_60,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_22]),
    [final]).

cnf(c_0_61,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(X2,X3,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_30]),
    [final]).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X1,esk1_2(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_21]),
    [final]).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_25]),
    [final]).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22]),
    [final]).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25]),
    [final]).

cnf(c_0_66,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_67,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_68,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47]),
    [final]).

cnf(c_0_69,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_48]),
    [final]).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_49]),
    [final]).

cnf(c_0_71,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k1_xboole_0,X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])]),c_0_22])]),
    [final]).

cnf(c_0_73,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51]),
    [final]).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52]),
    [final]).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_77,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relset_1(X3,X4,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_30]),
    [final]).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54]),
    [final]).

cnf(c_0_79,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_22]),
    [final]).

cnf(c_0_80,plain,
    ( v5_relat_1(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_81,plain,
    ( v4_relat_1(esk1_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_82,plain,
    ( v1_relat_1(esk1_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( v23_waybel_0(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_84,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_85,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.13/0.38  # and selection function SelectNewComplexAHPNS.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.032 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # No proof found!
% 0.13/0.38  # SZS status CounterSatisfiable
% 0.13/0.38  # SZS output start Saturation
% 0.13/0.38  fof(t67_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_waybel_0)).
% 0.13/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.38  fof(rc1_relset_1, axiom, ![X1, X2]:?[X3]:((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_xboole_0(X3))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 0.13/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.38  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.13/0.38  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:((~(v2_struct_0(X2))&l1_orders_2(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v23_waybel_0(X3,X1,X2)=>(((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))&k2_relat_1(k2_funct_1(X3))=u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t67_waybel_0])).
% 0.13/0.38  fof(c_0_13, plain, ![X18, X19, X20]:((((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))&((~v1_funct_2(X20,X18,X19)|X20=k1_xboole_0|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X20!=k1_xboole_0|v1_funct_2(X20,X18,X19)|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k1_relset_1(X15,X16,X17)=k1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.38  fof(c_0_15, plain, ![X21, X22]:((((m1_subset_1(esk1_2(X21,X22),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))&v1_xboole_0(esk1_2(X21,X22)))&v1_relat_1(esk1_2(X21,X22)))&v4_relat_1(esk1_2(X21,X22),X21))&v5_relat_1(esk1_2(X21,X22),X22)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).
% 0.13/0.38  fof(c_0_16, plain, ![X4]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X4)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.38  fof(c_0_17, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|v1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.38  fof(c_0_18, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_orders_2(esk2_0))&((~v2_struct_0(esk3_0)&l1_orders_2(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(v23_waybel_0(esk4_0,esk2_0,esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))|k2_relat_1(k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.13/0.38  cnf(c_0_19, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.13/0.38  cnf(c_0_21, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_22, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.13/0.38  fof(c_0_23, plain, ![X8]:((k2_relat_1(X8)=k1_relat_1(k2_funct_1(X8))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(k1_relat_1(X8)=k2_relat_1(k2_funct_1(X8))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  fof(c_0_26, plain, ![X12, X13, X14]:(~v1_xboole_0(X12)|(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.13/0.38  cnf(c_0_27, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_19]), ['final']).
% 0.13/0.38  cnf(c_0_28, plain, (k1_relset_1(X1,X2,esk1_2(X1,X2))=k1_relat_1(esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_29, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_30, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))|k2_relat_1(k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_32, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_35, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_25]), ['final']).
% 0.13/0.38  fof(c_0_38, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|m1_subset_1(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  cnf(c_0_39, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_26]), ['final']).
% 0.13/0.38  cnf(c_0_40, plain, (v1_funct_2(esk1_2(k1_xboole_0,X1),k1_xboole_0,X1)|k1_relat_1(esk1_2(k1_xboole_0,X1))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_21])]), ['final']).
% 0.13/0.38  cnf(c_0_41, plain, (X1=k1_xboole_0|v1_funct_2(esk1_2(X2,X1),X2,X1)|k1_relat_1(esk1_2(X2,X1))!=X2), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_21])]), ['final']).
% 0.13/0.38  cnf(c_0_42, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22])])]), ['final']).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk4_0)!=u1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(esk4_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_34])]), ['final']).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_25]), c_0_36])]), c_0_37]), ['final']).
% 0.13/0.38  cnf(c_0_45, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_30]), c_0_22])]), ['final']).
% 0.13/0.38  cnf(c_0_46, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_38]), ['final']).
% 0.13/0.38  fof(c_0_47, plain, ![X24, X25, X26]:(((v1_funct_1(k2_funct_1(X26))|(~v2_funct_1(X26)|k2_relset_1(X24,X25,X26)!=X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))&(v1_funct_2(k2_funct_1(X26),X25,X24)|(~v2_funct_1(X26)|k2_relset_1(X24,X25,X26)!=X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))))&(m1_subset_1(k2_funct_1(X26),k1_zfmisc_1(k2_zfmisc_1(X25,X24)))|(~v2_funct_1(X26)|k2_relset_1(X24,X25,X26)!=X25)|(~v1_funct_1(X26)|~v1_funct_2(X26,X24,X25)|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.13/0.38  cnf(c_0_48, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_49, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_50, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_51, plain, ![X27]:(v2_struct_0(X27)|~l1_struct_0(X27)|~v1_xboole_0(u1_struct_0(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  fof(c_0_52, plain, ![X28]:(~l1_orders_2(X28)|l1_struct_0(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.38  cnf(c_0_53, plain, (v1_xboole_0(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_22])).
% 0.13/0.38  cnf(c_0_54, plain, (v1_xboole_0(esk1_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_55, plain, (v1_funct_2(esk1_2(k1_xboole_0,X1),k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,esk1_2(k1_xboole_0,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_28]), ['final']).
% 0.13/0.38  cnf(c_0_56, plain, (X1=k1_xboole_0|v1_funct_2(esk1_2(X2,X1),X2,X1)|k1_relset_1(X2,X1,esk1_2(X2,X1))!=X2), inference(spm,[status(thm)],[c_0_41, c_0_28]), ['final']).
% 0.13/0.38  cnf(c_0_57, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,k1_relset_1(X2,X3,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_42, c_0_30]), ['final']).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(esk4_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_43, c_0_44]), ['final']).
% 0.13/0.38  cnf(c_0_59, plain, (k1_relset_1(X1,X2,esk1_2(X1,X2))=X1|X2=k1_xboole_0|~v1_funct_2(esk1_2(X1,X2),X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_60, plain, (k1_relset_1(X1,X2,k1_xboole_0)=X1|X2=k1_xboole_0|~v1_funct_2(k1_xboole_0,X1,X2)), inference(spm,[status(thm)],[c_0_35, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_61, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(X2,X3,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_30]), ['final']).
% 0.13/0.38  cnf(c_0_62, plain, (m1_subset_1(X1,k2_zfmisc_1(X2,X3))|~r2_hidden(X1,esk1_2(X2,X3))), inference(spm,[status(thm)],[c_0_46, c_0_21]), ['final']).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (m1_subset_1(X1,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_64, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_66, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_67, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_68, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47]), ['final']).
% 0.13/0.38  cnf(c_0_69, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_48]), ['final']).
% 0.13/0.38  cnf(c_0_70, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_49]), ['final']).
% 0.13/0.38  cnf(c_0_71, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_72, plain, (X1=k1_xboole_0|v1_funct_2(k1_xboole_0,X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])]), c_0_22])]), ['final']).
% 0.13/0.38  cnf(c_0_73, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_51]), ['final']).
% 0.13/0.38  cnf(c_0_74, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_52]), ['final']).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_77, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relset_1(X3,X4,k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_30]), ['final']).
% 0.13/0.38  cnf(c_0_78, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54]), ['final']).
% 0.13/0.38  cnf(c_0_79, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_22]), ['final']).
% 0.13/0.38  cnf(c_0_80, plain, (v5_relat_1(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_81, plain, (v4_relat_1(esk1_2(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_82, plain, (v1_relat_1(esk1_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.13/0.38  cnf(c_0_83, negated_conjecture, (v23_waybel_0(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  cnf(c_0_85, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 86
% 0.13/0.38  # Proof object clause steps            : 61
% 0.13/0.38  # Proof object formula steps           : 25
% 0.13/0.38  # Proof object conjectures             : 19
% 0.13/0.38  # Proof object clause conjectures      : 16
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 32
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 25
% 0.13/0.38  # Proof object simplifying inferences  : 23
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 32
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 32
% 0.13/0.38  # Processed clauses                    : 113
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 19
% 0.13/0.38  # ...remaining for further processing  : 93
% 0.13/0.38  # Other redundant clauses eliminated   : 8
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 1
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 56
% 0.13/0.38  # ...of the previous two non-trivial   : 50
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 49
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 8
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 56
% 0.13/0.38  #    Positive orientable unit clauses  : 16
% 0.13/0.38  #    Positive unorientable unit clauses: 3
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 35
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 33
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 370
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 97
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.13/0.38  # Unit Clause-clause subsumption calls : 23
% 0.13/0.38  # Rewrite failures with RHS unbound    : 26
% 0.13/0.38  # BW rewrite match attempts            : 28
% 0.13/0.38  # BW rewrite match successes           : 5
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3237
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.035 s
% 0.13/0.38  # System time              : 0.010 s
% 0.13/0.38  # Total time               : 0.045 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
