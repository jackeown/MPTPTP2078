%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:33 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 180 expanded)
%              Number of clauses        :   34 (  66 expanded)
%              Number of leaves         :   10 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  252 ( 849 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d11_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r1_waybel_0(X1,X2,X3)
            <=> ? [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                  & ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ( r1_orders_2(X2,X4,X5)
                       => r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(t8_waybel_9,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(t189_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( m1_subset_1(X3,X1)
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,X1,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                 => r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(dt_u1_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_waybel_0(X2,X1) )
     => ( v1_funct_1(u1_waybel_0(X1,X2))
        & v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

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

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

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

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X11,X10)
        | r2_hidden(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ r2_hidden(X11,X10)
        | m1_subset_1(X11,X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X11,X10)
        | v1_xboole_0(X11)
        | ~ v1_xboole_0(X10) )
      & ( ~ v1_xboole_0(X11)
        | m1_subset_1(X11,X10)
        | ~ v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_11,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X18,X19,X20,X22,X23,X24] :
      ( ( m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X19))
        | ~ r1_waybel_0(X18,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r1_orders_2(X19,esk2_3(X18,X19,X20),X22)
        | r2_hidden(k2_waybel_0(X18,X19,X22),X20)
        | ~ r1_waybel_0(X18,X19,X20)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( m1_subset_1(esk3_4(X18,X19,X23,X24),u1_struct_0(X19))
        | ~ m1_subset_1(X24,u1_struct_0(X19))
        | r1_waybel_0(X18,X19,X23)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( r1_orders_2(X19,X24,esk3_4(X18,X19,X23,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X19))
        | r1_waybel_0(X18,X19,X23)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) )
      & ( ~ r2_hidden(k2_waybel_0(X18,X19,esk3_4(X18,X19,X23,X24)),X23)
        | ~ m1_subset_1(X24,u1_struct_0(X19))
        | r1_waybel_0(X18,X19,X23)
        | v2_struct_0(X19)
        | ~ l1_waybel_0(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_struct_0(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_9])).

fof(c_0_18,plain,(
    ! [X12,X13,X14,X15] :
      ( v1_xboole_0(X12)
      | v1_xboole_0(X13)
      | ~ m1_subset_1(X14,X12)
      | ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,X12,X13)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | r2_hidden(k3_funct_2(X12,X13,X15,X14),k2_relset_1(X12,X13,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( ( v1_funct_1(u1_waybel_0(X31,X32))
        | ~ l1_struct_0(X31)
        | ~ l1_waybel_0(X32,X31) )
      & ( v1_funct_2(u1_waybel_0(X31,X32),u1_struct_0(X32),u1_struct_0(X31))
        | ~ l1_struct_0(X31)
        | ~ l1_waybel_0(X32,X31) )
      & ( m1_subset_1(u1_waybel_0(X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
        | ~ l1_struct_0(X31)
        | ~ l1_waybel_0(X32,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).

cnf(c_0_20,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X4,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_struct_0(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & l1_waybel_0(esk5_0,esk4_0)
    & ~ r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( v1_funct_1(u1_waybel_0(X1,X2))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | m1_subset_1(esk3_4(X1,X2,X3,esk1_1(u1_struct_0(X2))),u1_struct_0(X2))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( l1_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ l1_struct_0(X26)
      | v2_struct_0(X27)
      | ~ l1_waybel_0(X27,X26)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | k2_waybel_0(X26,X27,X28) = k3_funct_2(u1_struct_0(X27),u1_struct_0(X26),u1_waybel_0(X26,X27),X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
    | v1_xboole_0(u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | m1_subset_1(esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0))),u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_waybel_0(X1,X2,X3) = k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0),esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(X2))
    | ~ l1_waybel_0(esk5_0,X2)
    | ~ l1_struct_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),u1_waybel_0(X1,esk5_0),esk3_4(esk4_0,esk5_0,X2,esk1_1(u1_struct_0(esk5_0)))) = k2_waybel_0(X1,esk5_0,esk3_4(esk4_0,esk5_0,X2,esk1_1(u1_struct_0(esk5_0))))
    | r1_waybel_0(esk4_0,esk5_0,X2)
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ l1_waybel_0(esk5_0,X1)
    | ~ l1_struct_0(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0)))) = k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0))))
    | r1_waybel_0(esk4_0,esk5_0,X1)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_29])]),c_0_31])).

cnf(c_0_40,plain,
    ( r1_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( r1_waybel_0(esk4_0,esk5_0,X1)
    | r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_43,plain,(
    ! [X16] :
      ( v2_struct_0(X16)
      | ~ l1_struct_0(X16)
      | ~ v1_xboole_0(u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_1(u1_struct_0(esk5_0)),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_28]),c_0_29])]),c_0_42]),c_0_30]),c_0_31])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_21])).

fof(c_0_47,plain,(
    ! [X29,X30] :
      ( ~ l1_struct_0(X29)
      | ~ l1_waybel_0(X30,X29)
      | l1_orders_2(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29])]),c_0_31])).

fof(c_0_49,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_50,plain,
    ( l1_orders_2(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_48]),c_0_30])).

cnf(c_0_52,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_29])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:38:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.038 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.40  fof(d11_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r1_waybel_0(X1,X2,X3)<=>?[X4]:(m1_subset_1(X4,u1_struct_0(X2))&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r1_orders_2(X2,X4,X5)=>r2_hidden(k2_waybel_0(X1,X2,X5),X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_waybel_0)).
% 0.14/0.40  fof(t8_waybel_9, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_9)).
% 0.14/0.40  fof(t189_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,X1)=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_funct_2)).
% 0.14/0.40  fof(dt_u1_waybel_0, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_waybel_0(X2,X1))=>((v1_funct_1(u1_waybel_0(X1,X2))&v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 0.14/0.40  fof(d8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_waybel_0)).
% 0.14/0.40  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.40  fof(dt_l1_waybel_0, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_waybel_0(X2,X1)=>l1_orders_2(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 0.14/0.40  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.40  fof(c_0_10, plain, ![X10, X11]:(((~m1_subset_1(X11,X10)|r2_hidden(X11,X10)|v1_xboole_0(X10))&(~r2_hidden(X11,X10)|m1_subset_1(X11,X10)|v1_xboole_0(X10)))&((~m1_subset_1(X11,X10)|v1_xboole_0(X11)|~v1_xboole_0(X10))&(~v1_xboole_0(X11)|m1_subset_1(X11,X10)|~v1_xboole_0(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.40  fof(c_0_11, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.40  fof(c_0_12, plain, ![X18, X19, X20, X22, X23, X24]:(((m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X19))|~r1_waybel_0(X18,X19,X20)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18)))&(~m1_subset_1(X22,u1_struct_0(X19))|(~r1_orders_2(X19,esk2_3(X18,X19,X20),X22)|r2_hidden(k2_waybel_0(X18,X19,X22),X20))|~r1_waybel_0(X18,X19,X20)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18))))&((m1_subset_1(esk3_4(X18,X19,X23,X24),u1_struct_0(X19))|~m1_subset_1(X24,u1_struct_0(X19))|r1_waybel_0(X18,X19,X23)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18)))&((r1_orders_2(X19,X24,esk3_4(X18,X19,X23,X24))|~m1_subset_1(X24,u1_struct_0(X19))|r1_waybel_0(X18,X19,X23)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18)))&(~r2_hidden(k2_waybel_0(X18,X19,esk3_4(X18,X19,X23,X24)),X23)|~m1_subset_1(X24,u1_struct_0(X19))|r1_waybel_0(X18,X19,X23)|(v2_struct_0(X19)|~l1_waybel_0(X19,X18))|(v2_struct_0(X18)|~l1_struct_0(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_waybel_0])])])])])])])).
% 0.14/0.40  cnf(c_0_13, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.40  cnf(c_0_14, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  cnf(c_0_15, plain, (m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_16, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.40  fof(c_0_17, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_9])).
% 0.14/0.40  fof(c_0_18, plain, ![X12, X13, X14, X15]:(v1_xboole_0(X12)|(v1_xboole_0(X13)|(~m1_subset_1(X14,X12)|(~v1_funct_1(X15)|~v1_funct_2(X15,X12,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|r2_hidden(k3_funct_2(X12,X13,X15,X14),k2_relset_1(X12,X13,X15)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t189_funct_2])])])])).
% 0.14/0.40  fof(c_0_19, plain, ![X31, X32]:(((v1_funct_1(u1_waybel_0(X31,X32))|(~l1_struct_0(X31)|~l1_waybel_0(X32,X31)))&(v1_funct_2(u1_waybel_0(X31,X32),u1_struct_0(X32),u1_struct_0(X31))|(~l1_struct_0(X31)|~l1_waybel_0(X32,X31))))&(m1_subset_1(u1_waybel_0(X31,X32),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|(~l1_struct_0(X31)|~l1_waybel_0(X32,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_waybel_0])])])).
% 0.14/0.40  cnf(c_0_20, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(esk3_4(X1,X2,X3,X4),u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)|~r2_hidden(X4,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.40  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.40  fof(c_0_22, negated_conjecture, ((~v2_struct_0(esk4_0)&l1_struct_0(esk4_0))&((~v2_struct_0(esk5_0)&l1_waybel_0(esk5_0,esk4_0))&~r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.14/0.40  cnf(c_0_23, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r2_hidden(k3_funct_2(X1,X2,X4,X3),k2_relset_1(X1,X2,X4))|~m1_subset_1(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.40  cnf(c_0_24, plain, (m1_subset_1(u1_waybel_0(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_25, plain, (v1_funct_1(u1_waybel_0(X1,X2))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_26, plain, (v1_funct_2(u1_waybel_0(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_27, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|m1_subset_1(esk3_4(X1,X2,X3,esk1_1(u1_struct_0(X2))),u1_struct_0(X2))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.14/0.40  cnf(c_0_28, negated_conjecture, (l1_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_29, negated_conjecture, (l1_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  fof(c_0_32, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~l1_struct_0(X26)|(v2_struct_0(X27)|~l1_waybel_0(X27,X26)|(~m1_subset_1(X28,u1_struct_0(X27))|k2_waybel_0(X26,X27,X28)=k3_funct_2(u1_struct_0(X27),u1_struct_0(X26),u1_waybel_0(X26,X27),X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_waybel_0])])])])).
% 0.14/0.40  cnf(c_0_33, plain, (r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1),X3),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))|v1_xboole_0(u1_struct_0(X1))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.14/0.40  cnf(c_0_34, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|m1_subset_1(esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0))),u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.14/0.40  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_waybel_0(X1,X2,X3)=k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),u1_waybel_0(X1,X2),X3)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.40  cnf(c_0_36, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0),esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(X2),u1_waybel_0(X2,esk5_0)))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(X2))|~l1_waybel_0(esk5_0,X2)|~l1_struct_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.14/0.40  cnf(c_0_37, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(X1),u1_waybel_0(X1,esk5_0),esk3_4(esk4_0,esk5_0,X2,esk1_1(u1_struct_0(esk5_0))))=k2_waybel_0(X1,esk5_0,esk3_4(esk4_0,esk5_0,X2,esk1_1(u1_struct_0(esk5_0))))|r1_waybel_0(esk4_0,esk5_0,X2)|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(esk5_0))|~l1_waybel_0(esk5_0,X1)|~l1_struct_0(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_30])).
% 0.14/0.40  cnf(c_0_38, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|r2_hidden(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_29])])).
% 0.14/0.40  cnf(c_0_39, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0),esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0))))=k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0))))|r1_waybel_0(esk4_0,esk5_0,X1)|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_29])]), c_0_31])).
% 0.14/0.40  cnf(c_0_40, plain, (r1_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|~m1_subset_1(X4,u1_struct_0(X2))|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_41, negated_conjecture, (r1_waybel_0(esk4_0,esk5_0,X1)|r2_hidden(k2_waybel_0(esk4_0,esk5_0,esk3_4(esk4_0,esk5_0,X1,esk1_1(u1_struct_0(esk5_0)))),k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.40  cnf(c_0_42, negated_conjecture, (~r1_waybel_0(esk4_0,esk5_0,k2_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_waybel_0(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  fof(c_0_43, plain, ![X16]:(v2_struct_0(X16)|~l1_struct_0(X16)|~v1_xboole_0(u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.40  cnf(c_0_44, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(esk1_1(u1_struct_0(esk5_0)),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_28]), c_0_29])]), c_0_42]), c_0_30]), c_0_31])).
% 0.14/0.40  cnf(c_0_45, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.40  cnf(c_0_46, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_21])).
% 0.14/0.40  fof(c_0_47, plain, ![X29, X30]:(~l1_struct_0(X29)|(~l1_waybel_0(X30,X29)|l1_orders_2(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_waybel_0])])])).
% 0.14/0.40  cnf(c_0_48, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_29])]), c_0_31])).
% 0.14/0.40  fof(c_0_49, plain, ![X17]:(~l1_orders_2(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.40  cnf(c_0_50, plain, (l1_orders_2(X2)|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.14/0.40  cnf(c_0_51, negated_conjecture, (~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_48]), c_0_30])).
% 0.14/0.40  cnf(c_0_52, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.40  cnf(c_0_53, negated_conjecture, (l1_orders_2(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_29])])).
% 0.14/0.40  cnf(c_0_54, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 55
% 0.14/0.40  # Proof object clause steps            : 34
% 0.14/0.40  # Proof object formula steps           : 21
% 0.14/0.40  # Proof object conjectures             : 20
% 0.14/0.40  # Proof object clause conjectures      : 17
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 18
% 0.14/0.40  # Proof object initial formulas used   : 10
% 0.14/0.40  # Proof object generating inferences   : 15
% 0.14/0.40  # Proof object simplifying inferences  : 28
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 10
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 24
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 24
% 0.14/0.40  # Processed clauses                    : 104
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 9
% 0.14/0.40  # ...remaining for further processing  : 95
% 0.14/0.40  # Other redundant clauses eliminated   : 0
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 12
% 0.14/0.40  # Backward-rewritten                   : 13
% 0.14/0.40  # Generated clauses                    : 88
% 0.14/0.40  # ...of the previous two non-trivial   : 75
% 0.14/0.40  # Contextual simplify-reflections      : 6
% 0.14/0.40  # Paramodulations                      : 88
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 0
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 46
% 0.14/0.40  #    Positive orientable unit clauses  : 4
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 4
% 0.14/0.40  #    Non-unit-clauses                  : 38
% 0.14/0.40  # Current number of unprocessed clauses: 19
% 0.14/0.40  # ...number of literals in the above   : 116
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 49
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 1516
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 299
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 27
% 0.14/0.40  # Unit Clause-clause subsumption calls : 20
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 1
% 0.14/0.40  # BW rewrite match successes           : 1
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 5976
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.055 s
% 0.14/0.40  # System time              : 0.004 s
% 0.14/0.40  # Total time               : 0.059 s
% 0.14/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
