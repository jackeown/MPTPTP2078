%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 309 expanded)
%              Number of clauses        :   38 ( 112 expanded)
%              Number of leaves         :   10 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 (1312 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_yellow_6,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( l1_waybel_0(X3,X1)
             => ( m1_yellow_6(X3,X1,X2)
              <=> ( m1_yellow_0(X3,X2)
                  & u1_waybel_0(X1,X3) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

fof(dt_m1_yellow_6,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ! [X3] :
          ( m1_yellow_6(X3,X1,X2)
         => l1_waybel_0(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_6)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t18_yellow_6,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_6(X3,X1,X2)
             => ! [X4] :
                  ( m1_yellow_6(X4,X1,X3)
                 => m1_yellow_6(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_6)).

fof(t82_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,X1)
          & k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_funct_1)).

fof(d13_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( m1_yellow_0(X2,X1)
          <=> ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
              & r1_tarski(u1_orders_2(X2),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

fof(dt_l1_waybel_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_waybel_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(t16_yellow_6,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ! [X3] :
              ( m1_yellow_0(X3,X2)
             => m1_yellow_0(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_6)).

fof(c_0_10,plain,(
    ! [X21,X22,X23] :
      ( ( m1_yellow_0(X23,X22)
        | ~ m1_yellow_6(X23,X21,X22)
        | ~ l1_waybel_0(X23,X21)
        | ~ l1_waybel_0(X22,X21)
        | ~ l1_struct_0(X21) )
      & ( u1_waybel_0(X21,X23) = k2_partfun1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22),u1_struct_0(X23))
        | ~ m1_yellow_6(X23,X21,X22)
        | ~ l1_waybel_0(X23,X21)
        | ~ l1_waybel_0(X22,X21)
        | ~ l1_struct_0(X21) )
      & ( ~ m1_yellow_0(X23,X22)
        | u1_waybel_0(X21,X23) != k2_partfun1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22),u1_struct_0(X23))
        | m1_yellow_6(X23,X21,X22)
        | ~ l1_waybel_0(X23,X21)
        | ~ l1_waybel_0(X22,X21)
        | ~ l1_struct_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).

fof(c_0_11,plain,(
    ! [X24,X25,X26] :
      ( ~ l1_struct_0(X24)
      | ~ l1_waybel_0(X25,X24)
      | ~ m1_yellow_6(X26,X24,X25)
      | l1_waybel_0(X26,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).

fof(c_0_12,plain,(
    ! [X11,X12,X13,X14] :
      ( ~ v1_funct_1(X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | k2_partfun1(X11,X12,X13,X14) = k7_relat_1(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ( v1_funct_1(u1_waybel_0(X19,X20))
        | ~ l1_struct_0(X19)
        | ~ l1_waybel_0(X20,X19) )
      & ( v1_funct_2(u1_waybel_0(X19,X20),u1_struct_0(X20),u1_struct_0(X19))
        | ~ l1_struct_0(X19)
        | ~ l1_waybel_0(X20,X19) )
      & ( m1_subset_1(u1_waybel_0(X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))
        | ~ l1_struct_0(X19)
        | ~ l1_waybel_0(X20,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_14,plain,
    ( u1_waybel_0(X1,X2) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),u1_struct_0(X2))
    | ~ m1_yellow_6(X2,X1,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( l1_waybel_0(X3,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_yellow_6(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_waybel_0(X2,X1)
           => ! [X3] :
                ( m1_yellow_6(X3,X1,X2)
               => ! [X4] :
                    ( m1_yellow_6(X4,X1,X3)
                   => m1_yellow_6(X4,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_yellow_6])).

fof(c_0_21,plain,(
    ! [X5,X6,X7] :
      ( ( k7_relat_1(k7_relat_1(X7,X5),X6) = k7_relat_1(X7,X5)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( k7_relat_1(k7_relat_1(X7,X6),X5) = k7_relat_1(X7,X5)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t82_funct_1])])])).

cnf(c_0_22,plain,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X3)) = u1_waybel_0(X2,X3)
    | ~ m1_yellow_6(X3,X2,X1)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3) = k7_relat_1(u1_waybel_0(X2,X1),X3)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_waybel_0(esk2_0,esk1_0)
    & m1_yellow_6(esk3_0,esk1_0,esk2_0)
    & m1_yellow_6(esk4_0,esk1_0,esk3_0)
    & ~ m1_yellow_6(esk4_0,esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_26,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,X3)
    | ~ r1_tarski(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k7_relat_1(u1_waybel_0(X1,X2),u1_struct_0(X3)) = u1_waybel_0(X1,X3)
    | ~ m1_yellow_6(X3,X1,X2)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( v1_relat_1(u1_waybel_0(X1,X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_17])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(u1_struct_0(X16),u1_struct_0(X15))
        | ~ m1_yellow_0(X16,X15)
        | ~ l1_orders_2(X16)
        | ~ l1_orders_2(X15) )
      & ( r1_tarski(u1_orders_2(X16),u1_orders_2(X15))
        | ~ m1_yellow_0(X16,X15)
        | ~ l1_orders_2(X16)
        | ~ l1_orders_2(X15) )
      & ( ~ r1_tarski(u1_struct_0(X16),u1_struct_0(X15))
        | ~ r1_tarski(u1_orders_2(X16),u1_orders_2(X15))
        | m1_yellow_0(X16,X15)
        | ~ l1_orders_2(X16)
        | ~ l1_orders_2(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ~ l1_struct_0(X17)
      | ~ l1_waybel_0(X18,X17)
      | l1_orders_2(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_yellow_6(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( l1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k7_relat_1(u1_waybel_0(X1,X2),X3) = k7_relat_1(u1_waybel_0(X1,X4),X3)
    | ~ m1_yellow_6(X2,X1,X4)
    | ~ l1_waybel_0(X4,X1)
    | ~ l1_struct_0(X1)
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_18])).

cnf(c_0_35,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( l1_waybel_0(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_38,plain,
    ( k7_relat_1(u1_waybel_0(X1,X2),u1_struct_0(X3)) = k7_relat_1(u1_waybel_0(X1,X4),u1_struct_0(X3))
    | ~ m1_yellow_6(X2,X1,X4)
    | ~ l1_waybel_0(X4,X1)
    | ~ l1_struct_0(X1)
    | ~ m1_yellow_0(X3,X2)
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33])])).

cnf(c_0_40,plain,
    ( m1_yellow_6(X1,X3,X2)
    | ~ m1_yellow_0(X1,X2)
    | u1_waybel_0(X3,X1) != k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_waybel_0(X3,X2),u1_struct_0(X1))
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(u1_waybel_0(esk1_0,esk3_0),u1_struct_0(X1)) = k7_relat_1(u1_waybel_0(esk1_0,esk2_0),u1_struct_0(X1))
    | ~ m1_yellow_0(X1,esk3_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_32]),c_0_33]),c_0_39])])).

cnf(c_0_42,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X1,X3)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( m1_yellow_6(esk4_0,esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( m1_yellow_6(X1,X2,X3)
    | k7_relat_1(u1_waybel_0(X2,X3),u1_struct_0(X1)) != u1_waybel_0(X2,X1)
    | ~ l1_waybel_0(X3,X2)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_yellow_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_40,c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(u1_waybel_0(esk1_0,esk2_0),u1_struct_0(X1)) = u1_waybel_0(esk1_0,X1)
    | ~ m1_yellow_6(X1,esk1_0,esk3_0)
    | ~ m1_yellow_0(X1,esk3_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_41]),c_0_37]),c_0_33])])).

cnf(c_0_46,plain,
    ( m1_yellow_0(X1,X2)
    | ~ m1_yellow_6(X1,X3,X2)
    | ~ l1_waybel_0(X2,X3)
    | ~ l1_struct_0(X3) ),
    inference(csr,[status(thm)],[c_0_42,c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( l1_waybel_0(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_43]),c_0_33])]),c_0_37])])).

fof(c_0_48,plain,(
    ! [X27,X28,X29] :
      ( ~ l1_orders_2(X27)
      | ~ m1_yellow_0(X28,X27)
      | ~ m1_yellow_0(X29,X28)
      | m1_yellow_0(X29,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_6])])])).

cnf(c_0_49,negated_conjecture,
    ( m1_yellow_6(X1,esk1_0,esk2_0)
    | ~ m1_yellow_6(X1,esk1_0,esk3_0)
    | ~ l1_waybel_0(X1,esk1_0)
    | ~ m1_yellow_0(X1,esk2_0)
    | ~ m1_yellow_0(X1,esk3_0)
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_32]),c_0_33])])).

cnf(c_0_50,negated_conjecture,
    ( m1_yellow_0(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_43]),c_0_37]),c_0_33])])).

cnf(c_0_51,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_47]),c_0_33])])).

cnf(c_0_52,negated_conjecture,
    ( ~ m1_yellow_6(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_53,plain,
    ( m1_yellow_0(X3,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ m1_yellow_0(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_yellow_0(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_43]),c_0_47]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( m1_yellow_0(esk4_0,X1)
    | ~ m1_yellow_0(esk3_0,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_57,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_33])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.55  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.55  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.55  #
% 0.20/0.55  # Preprocessing time       : 0.028 s
% 0.20/0.55  # Presaturation interreduction done
% 0.20/0.55  
% 0.20/0.55  # Proof found!
% 0.20/0.55  # SZS status Theorem
% 0.20/0.55  # SZS output start CNFRefutation
% 0.20/0.55  fof(d8_yellow_6, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(l1_waybel_0(X3,X1)=>(m1_yellow_6(X3,X1,X2)<=>(m1_yellow_0(X3,X2)&u1_waybel_0(X1,X3)=k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_6)).
% 0.20/0.55  fof(dt_m1_yellow_6, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>![X3]:(m1_yellow_6(X3,X1,X2)=>l1_waybel_0(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 0.20/0.55  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.20/0.55  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.20/0.55  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.55  fof(t18_yellow_6, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_yellow_6(X4,X1,X3)=>m1_yellow_6(X4,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_yellow_6)).
% 0.20/0.55  fof(t82_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r1_tarski(X1,X2)=>(k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,X1)&k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_funct_1)).
% 0.20/0.55  fof(d13_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(m1_yellow_0(X2,X1)<=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X1))&r1_tarski(u1_orders_2(X2),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 0.20/0.55  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.20/0.55  fof(t16_yellow_6, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_yellow_0(X2,X1)=>![X3]:(m1_yellow_0(X3,X2)=>m1_yellow_0(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_yellow_6)).
% 0.20/0.55  fof(c_0_10, plain, ![X21, X22, X23]:(((m1_yellow_0(X23,X22)|~m1_yellow_6(X23,X21,X22)|~l1_waybel_0(X23,X21)|~l1_waybel_0(X22,X21)|~l1_struct_0(X21))&(u1_waybel_0(X21,X23)=k2_partfun1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22),u1_struct_0(X23))|~m1_yellow_6(X23,X21,X22)|~l1_waybel_0(X23,X21)|~l1_waybel_0(X22,X21)|~l1_struct_0(X21)))&(~m1_yellow_0(X23,X22)|u1_waybel_0(X21,X23)!=k2_partfun1(u1_struct_0(X22),u1_struct_0(X21),u1_waybel_0(X21,X22),u1_struct_0(X23))|m1_yellow_6(X23,X21,X22)|~l1_waybel_0(X23,X21)|~l1_waybel_0(X22,X21)|~l1_struct_0(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_yellow_6])])])])).
% 0.20/0.55  fof(c_0_11, plain, ![X24, X25, X26]:(~l1_struct_0(X24)|~l1_waybel_0(X25,X24)|(~m1_yellow_6(X26,X24,X25)|l1_waybel_0(X26,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_6])])])).
% 0.20/0.55  fof(c_0_12, plain, ![X11, X12, X13, X14]:(~v1_funct_1(X13)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|k2_partfun1(X11,X12,X13,X14)=k7_relat_1(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.20/0.55  fof(c_0_13, plain, ![X19, X20]:(((v1_funct_1(u1_waybel_0(X19,X20))|(~l1_struct_0(X19)|~l1_waybel_0(X20,X19)))&(v1_funct_2(u1_waybel_0(X19,X20),u1_struct_0(X20),u1_struct_0(X19))|(~l1_struct_0(X19)|~l1_waybel_0(X20,X19))))&(m1_subset_1(u1_waybel_0(X19,X20),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))|(~l1_struct_0(X19)|~l1_waybel_0(X20,X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.20/0.55  cnf(c_0_14, plain, (u1_waybel_0(X1,X2)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),u1_struct_0(X2))|~m1_yellow_6(X2,X1,X3)|~l1_waybel_0(X2,X1)|~l1_waybel_0(X3,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_15, plain, (l1_waybel_0(X3,X1)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_yellow_6(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.55  cnf(c_0_16, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.55  cnf(c_0_17, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.55  cnf(c_0_18, plain, (v1_funct_1(u1_waybel_0(X1,X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.55  fof(c_0_19, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|v1_relat_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.55  fof(c_0_20, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>![X3]:(m1_yellow_6(X3,X1,X2)=>![X4]:(m1_yellow_6(X4,X1,X3)=>m1_yellow_6(X4,X1,X2)))))), inference(assume_negation,[status(cth)],[t18_yellow_6])).
% 0.20/0.55  fof(c_0_21, plain, ![X5, X6, X7]:((k7_relat_1(k7_relat_1(X7,X5),X6)=k7_relat_1(X7,X5)|~r1_tarski(X5,X6)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(k7_relat_1(k7_relat_1(X7,X6),X5)=k7_relat_1(X7,X5)|~r1_tarski(X5,X6)|(~v1_relat_1(X7)|~v1_funct_1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t82_funct_1])])])).
% 0.20/0.55  cnf(c_0_22, plain, (k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),u1_struct_0(X3))=u1_waybel_0(X2,X3)|~m1_yellow_6(X3,X2,X1)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)), inference(csr,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.55  cnf(c_0_23, plain, (k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3)=k7_relat_1(u1_waybel_0(X2,X1),X3)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.20/0.55  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.55  fof(c_0_25, negated_conjecture, (l1_struct_0(esk1_0)&(l1_waybel_0(esk2_0,esk1_0)&(m1_yellow_6(esk3_0,esk1_0,esk2_0)&(m1_yellow_6(esk4_0,esk1_0,esk3_0)&~m1_yellow_6(esk4_0,esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.20/0.55  cnf(c_0_26, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,X3)|~r1_tarski(X3,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.55  cnf(c_0_27, plain, (k7_relat_1(u1_waybel_0(X1,X2),u1_struct_0(X3))=u1_waybel_0(X1,X3)|~m1_yellow_6(X3,X1,X2)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.55  cnf(c_0_28, plain, (v1_relat_1(u1_waybel_0(X1,X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_17])).
% 0.20/0.55  fof(c_0_29, plain, ![X15, X16]:(((r1_tarski(u1_struct_0(X16),u1_struct_0(X15))|~m1_yellow_0(X16,X15)|~l1_orders_2(X16)|~l1_orders_2(X15))&(r1_tarski(u1_orders_2(X16),u1_orders_2(X15))|~m1_yellow_0(X16,X15)|~l1_orders_2(X16)|~l1_orders_2(X15)))&(~r1_tarski(u1_struct_0(X16),u1_struct_0(X15))|~r1_tarski(u1_orders_2(X16),u1_orders_2(X15))|m1_yellow_0(X16,X15)|~l1_orders_2(X16)|~l1_orders_2(X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_yellow_0])])])])).
% 0.20/0.55  fof(c_0_30, plain, ![X17, X18]:(~l1_struct_0(X17)|(~l1_waybel_0(X18,X17)|l1_orders_2(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.20/0.55  cnf(c_0_31, negated_conjecture, (m1_yellow_6(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  cnf(c_0_32, negated_conjecture, (l1_waybel_0(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  cnf(c_0_33, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  cnf(c_0_34, plain, (k7_relat_1(u1_waybel_0(X1,X2),X3)=k7_relat_1(u1_waybel_0(X1,X4),X3)|~m1_yellow_6(X2,X1,X4)|~l1_waybel_0(X4,X1)|~l1_struct_0(X1)|~r1_tarski(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_18])).
% 0.20/0.55  cnf(c_0_35, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_yellow_0(X1,X2)|~l1_orders_2(X1)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.55  cnf(c_0_36, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.55  cnf(c_0_37, negated_conjecture, (l1_waybel_0(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_31]), c_0_32]), c_0_33])])).
% 0.20/0.55  cnf(c_0_38, plain, (k7_relat_1(u1_waybel_0(X1,X2),u1_struct_0(X3))=k7_relat_1(u1_waybel_0(X1,X4),u1_struct_0(X3))|~m1_yellow_6(X2,X1,X4)|~l1_waybel_0(X4,X1)|~l1_struct_0(X1)|~m1_yellow_0(X3,X2)|~l1_orders_2(X2)|~l1_orders_2(X3)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.55  cnf(c_0_39, negated_conjecture, (l1_orders_2(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_33])])).
% 0.20/0.55  cnf(c_0_40, plain, (m1_yellow_6(X1,X3,X2)|~m1_yellow_0(X1,X2)|u1_waybel_0(X3,X1)!=k2_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_waybel_0(X3,X2),u1_struct_0(X1))|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_41, negated_conjecture, (k7_relat_1(u1_waybel_0(esk1_0,esk3_0),u1_struct_0(X1))=k7_relat_1(u1_waybel_0(esk1_0,esk2_0),u1_struct_0(X1))|~m1_yellow_0(X1,esk3_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_32]), c_0_33]), c_0_39])])).
% 0.20/0.55  cnf(c_0_42, plain, (m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X1,X3)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.55  cnf(c_0_43, negated_conjecture, (m1_yellow_6(esk4_0,esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  cnf(c_0_44, plain, (m1_yellow_6(X1,X2,X3)|k7_relat_1(u1_waybel_0(X2,X3),u1_struct_0(X1))!=u1_waybel_0(X2,X1)|~l1_waybel_0(X3,X2)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_yellow_0(X1,X3)), inference(spm,[status(thm)],[c_0_40, c_0_23])).
% 0.20/0.55  cnf(c_0_45, negated_conjecture, (k7_relat_1(u1_waybel_0(esk1_0,esk2_0),u1_struct_0(X1))=u1_waybel_0(esk1_0,X1)|~m1_yellow_6(X1,esk1_0,esk3_0)|~m1_yellow_0(X1,esk3_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_41]), c_0_37]), c_0_33])])).
% 0.20/0.55  cnf(c_0_46, plain, (m1_yellow_0(X1,X2)|~m1_yellow_6(X1,X3,X2)|~l1_waybel_0(X2,X3)|~l1_struct_0(X3)), inference(csr,[status(thm)],[c_0_42, c_0_15])).
% 0.20/0.55  cnf(c_0_47, negated_conjecture, (l1_waybel_0(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_43]), c_0_33])]), c_0_37])])).
% 0.20/0.55  fof(c_0_48, plain, ![X27, X28, X29]:(~l1_orders_2(X27)|(~m1_yellow_0(X28,X27)|(~m1_yellow_0(X29,X28)|m1_yellow_0(X29,X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_6])])])).
% 0.20/0.55  cnf(c_0_49, negated_conjecture, (m1_yellow_6(X1,esk1_0,esk2_0)|~m1_yellow_6(X1,esk1_0,esk3_0)|~l1_waybel_0(X1,esk1_0)|~m1_yellow_0(X1,esk2_0)|~m1_yellow_0(X1,esk3_0)|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_32]), c_0_33])])).
% 0.20/0.55  cnf(c_0_50, negated_conjecture, (m1_yellow_0(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_43]), c_0_37]), c_0_33])])).
% 0.20/0.55  cnf(c_0_51, negated_conjecture, (l1_orders_2(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_47]), c_0_33])])).
% 0.20/0.55  cnf(c_0_52, negated_conjecture, (~m1_yellow_6(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.55  cnf(c_0_53, plain, (m1_yellow_0(X3,X1)|~l1_orders_2(X1)|~m1_yellow_0(X2,X1)|~m1_yellow_0(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.55  cnf(c_0_54, negated_conjecture, (~m1_yellow_0(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_43]), c_0_47]), c_0_50]), c_0_51])]), c_0_52])).
% 0.20/0.55  cnf(c_0_55, negated_conjecture, (m1_yellow_0(esk4_0,X1)|~m1_yellow_0(esk3_0,X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_53, c_0_50])).
% 0.20/0.55  cnf(c_0_56, negated_conjecture, (m1_yellow_0(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_32]), c_0_33])])).
% 0.20/0.55  cnf(c_0_57, negated_conjecture, (l1_orders_2(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_33])])).
% 0.20/0.55  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])]), ['proof']).
% 0.20/0.55  # SZS output end CNFRefutation
% 0.20/0.55  # Proof object total steps             : 59
% 0.20/0.55  # Proof object clause steps            : 38
% 0.20/0.55  # Proof object formula steps           : 21
% 0.20/0.55  # Proof object conjectures             : 21
% 0.20/0.55  # Proof object clause conjectures      : 18
% 0.20/0.55  # Proof object formula conjectures     : 3
% 0.20/0.55  # Proof object initial clauses used    : 17
% 0.20/0.55  # Proof object initial formulas used   : 10
% 0.20/0.55  # Proof object generating inferences   : 19
% 0.20/0.55  # Proof object simplifying inferences  : 42
% 0.20/0.55  # Training examples: 0 positive, 0 negative
% 0.20/0.55  # Parsed axioms                        : 10
% 0.20/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.55  # Initial clauses                      : 21
% 0.20/0.55  # Removed in clause preprocessing      : 0
% 0.20/0.55  # Initial clauses in saturation        : 21
% 0.20/0.55  # Processed clauses                    : 1253
% 0.20/0.55  # ...of these trivial                  : 9
% 0.20/0.55  # ...subsumed                          : 800
% 0.20/0.55  # ...remaining for further processing  : 444
% 0.20/0.55  # Other redundant clauses eliminated   : 0
% 0.20/0.55  # Clauses deleted for lack of memory   : 0
% 0.20/0.55  # Backward-subsumed                    : 46
% 0.20/0.55  # Backward-rewritten                   : 0
% 0.20/0.55  # Generated clauses                    : 5258
% 0.20/0.55  # ...of the previous two non-trivial   : 4979
% 0.20/0.55  # Contextual simplify-reflections      : 37
% 0.20/0.55  # Paramodulations                      : 5258
% 0.20/0.55  # Factorizations                       : 0
% 0.20/0.55  # Equation resolutions                 : 0
% 0.20/0.55  # Propositional unsat checks           : 0
% 0.20/0.55  #    Propositional check models        : 0
% 0.20/0.55  #    Propositional check unsatisfiable : 0
% 0.20/0.55  #    Propositional clauses             : 0
% 0.20/0.55  #    Propositional clauses after purity: 0
% 0.20/0.55  #    Propositional unsat core size     : 0
% 0.20/0.55  #    Propositional preprocessing time  : 0.000
% 0.20/0.55  #    Propositional encoding time       : 0.000
% 0.20/0.55  #    Propositional solver time         : 0.000
% 0.20/0.55  #    Success case prop preproc time    : 0.000
% 0.20/0.55  #    Success case prop encoding time   : 0.000
% 0.20/0.55  #    Success case prop solver time     : 0.000
% 0.20/0.55  # Current number of processed clauses  : 377
% 0.20/0.55  #    Positive orientable unit clauses  : 11
% 0.20/0.55  #    Positive unorientable unit clauses: 0
% 0.20/0.55  #    Negative unit clauses             : 4
% 0.20/0.55  #    Non-unit-clauses                  : 362
% 0.20/0.55  # Current number of unprocessed clauses: 3723
% 0.20/0.55  # ...number of literals in the above   : 40643
% 0.20/0.55  # Current number of archived formulas  : 0
% 0.20/0.55  # Current number of archived clauses   : 67
% 0.20/0.55  # Clause-clause subsumption calls (NU) : 27739
% 0.20/0.55  # Rec. Clause-clause subsumption calls : 2902
% 0.20/0.55  # Non-unit clause-clause subsumptions  : 406
% 0.20/0.55  # Unit Clause-clause subsumption calls : 460
% 0.20/0.55  # Rewrite failures with RHS unbound    : 0
% 0.20/0.55  # BW rewrite match attempts            : 2
% 0.20/0.55  # BW rewrite match successes           : 0
% 0.20/0.55  # Condensation attempts                : 0
% 0.20/0.55  # Condensation successes               : 0
% 0.20/0.55  # Termbank termtop insertions          : 176810
% 0.20/0.55  
% 0.20/0.55  # -------------------------------------------------
% 0.20/0.55  # User time                : 0.201 s
% 0.20/0.55  # System time              : 0.005 s
% 0.20/0.55  # Total time               : 0.206 s
% 0.20/0.55  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
