%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1687+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:35 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 944 expanded)
%              Number of clauses        :   46 ( 301 expanded)
%              Number of leaves         :   12 ( 234 expanded)
%              Depth                    :   13
%              Number of atoms          :  340 (8948 expanded)
%              Number of equality atoms :   61 ( 829 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   88 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_waybel_0)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t66_waybel_0,axiom,(
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
              <=> ( v2_funct_1(X3)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = u1_struct_0(X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X4,X5)
                          <=> r1_orders_2(X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_waybel_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k2_relset_1(X18,X19,X20) = k2_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & l1_orders_2(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & l1_orders_2(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & v23_waybel_0(esk5_0,esk3_0,esk4_0)
    & ( ~ v1_funct_1(k2_funct_1(esk5_0))
      | ~ v1_funct_2(k2_funct_1(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      | k2_relat_1(k2_funct_1(esk5_0)) != u1_struct_0(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( v2_funct_1(X25)
        | ~ v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( k2_relset_1(u1_struct_0(X23),u1_struct_0(X24),X25) = u1_struct_0(X24)
        | ~ v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,X26,X27)
        | r1_orders_2(X24,k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,X26),k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,X27))
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X24,k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,X26),k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,X27))
        | r1_orders_2(X23,X26,X27)
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk1_3(X23,X24,X25),u1_struct_0(X23))
        | ~ v2_funct_1(X25)
        | k2_relset_1(u1_struct_0(X23),u1_struct_0(X24),X25) != u1_struct_0(X24)
        | v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X23))
        | ~ v2_funct_1(X25)
        | k2_relset_1(u1_struct_0(X23),u1_struct_0(X24),X25) != u1_struct_0(X24)
        | v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r1_orders_2(X23,esk1_3(X23,X24,X25),esk2_3(X23,X24,X25))
        | ~ r1_orders_2(X24,k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,esk1_3(X23,X24,X25)),k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,esk2_3(X23,X24,X25)))
        | ~ v2_funct_1(X25)
        | k2_relset_1(u1_struct_0(X23),u1_struct_0(X24),X25) != u1_struct_0(X24)
        | v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_orders_2(X23,esk1_3(X23,X24,X25),esk2_3(X23,X24,X25))
        | r1_orders_2(X24,k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,esk1_3(X23,X24,X25)),k3_funct_2(u1_struct_0(X23),u1_struct_0(X24),X25,esk2_3(X23,X24,X25)))
        | ~ v2_funct_1(X25)
        | k2_relset_1(u1_struct_0(X23),u1_struct_0(X24),X25) != u1_struct_0(X24)
        | v23_waybel_0(X25,X23,X24)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_waybel_0])])])])])])).

cnf(c_0_16,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_relset_1(X15,X16,X17) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_19,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = u1_struct_0(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v23_waybel_0(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v23_waybel_0(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
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

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(esk4_0) = k2_relat_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_17])]),c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_17])).

fof(c_0_32,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_33,plain,(
    ! [X22] :
      ( ( k2_relat_1(X22) = k1_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_relat_1(X22) = k2_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_34,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),k2_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),k2_relat_1(esk5_0),esk5_0) = k1_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k2_relat_1(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_30])).

cnf(c_0_38,plain,
    ( v2_funct_1(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v23_waybel_0(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X21] :
      ( ( v1_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_2(X21,k1_relat_1(X21),k2_relat_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X21),k2_relat_1(X21))))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_41,plain,(
    ! [X12] :
      ( ( v1_relat_1(k2_funct_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v1_funct_1(k2_funct_1(X12))
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_42,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk5_0) = u1_struct_0(esk3_0)
    | k2_relat_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_44,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_20]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_17])]),c_0_26]),c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_17])).

cnf(c_0_46,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = u1_struct_0(esk3_0)
    | k2_relat_1(esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_24]),c_0_45])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(k2_funct_1(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | k2_relat_1(k2_funct_1(esk5_0)) != u1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

fof(c_0_54,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),u1_struct_0(esk3_0))))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) != u1_struct_0(esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(k2_funct_1(esk5_0),k2_relat_1(esk5_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_30]),c_0_30])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),k2_relat_1(esk5_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_44]),c_0_24]),c_0_45])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_59,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),u1_struct_0(esk3_0))))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_24]),c_0_45])])).

cnf(c_0_61,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_30]),c_0_26])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_49]),c_0_24]),c_0_45])])).

cnf(c_0_65,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_49]),c_0_24]),c_0_45])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_22])])).

cnf(c_0_67,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_47]),c_0_44]),c_0_24]),c_0_45])]),c_0_65])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),
    [proof]).

%------------------------------------------------------------------------------
