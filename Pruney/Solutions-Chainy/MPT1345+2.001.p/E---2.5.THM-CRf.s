%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:04 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 838 expanded)
%              Number of clauses        :   67 ( 278 expanded)
%              Number of leaves         :   15 ( 209 expanded)
%              Depth                    :   17
%              Number of atoms          :  474 (5546 expanded)
%              Number of equality atoms :   85 ( 281 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d5_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & v5_pre_topc(X3,X1,X2)
                  & v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

fof(t70_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
               => v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t62_tops_2,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

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

fof(c_0_15,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k1_relset_1(X18,X19,X20) = k1_relat_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,plain,(
    ! [X29,X30,X31] :
      ( ( k1_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31) = k2_struct_0(X29)
        | ~ v3_tops_2(X31,X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) )
      & ( k2_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31) = k2_struct_0(X30)
        | ~ v3_tops_2(X31,X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) )
      & ( v2_funct_1(X31)
        | ~ v3_tops_2(X31,X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) )
      & ( v5_pre_topc(X31,X29,X30)
        | ~ v3_tops_2(X31,X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X29),u1_struct_0(X30),X31),X30,X29)
        | ~ v3_tops_2(X31,X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) )
      & ( k1_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31) != k2_struct_0(X29)
        | k2_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31) != k2_struct_0(X30)
        | ~ v2_funct_1(X31)
        | ~ v5_pre_topc(X31,X29,X30)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X29),u1_struct_0(X30),X31),X30,X29)
        | v3_tops_2(X31,X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30))))
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v3_tops_2(X3,X1,X2)
                 => v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_tops_2])).

cnf(c_0_18,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v3_tops_2(esk3_0,esk1_0,esk2_0)
    & ~ v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ( ~ v4_relat_1(X9,X8)
        | r1_tarski(k1_relat_1(X9),X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k1_relat_1(X9),X8)
        | v4_relat_1(X9,X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_23,plain,
    ( k2_struct_0(X1) = k1_relat_1(X2)
    | ~ v3_tops_2(X2,X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v3_tops_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_31,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | k2_struct_0(X24) = u1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_32,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_33,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk3_0) = k2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_38,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X15,X16,X17] :
      ( ( v4_relat_1(X17,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v5_relat_1(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_43,plain,(
    ! [X32,X33,X34] :
      ( ( k1_relset_1(u1_struct_0(X33),u1_struct_0(X32),k2_tops_2(u1_struct_0(X32),u1_struct_0(X33),X34)) = k2_struct_0(X33)
        | k2_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34) != k2_struct_0(X33)
        | ~ v2_funct_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33)
        | ~ l1_struct_0(X32) )
      & ( k2_relset_1(u1_struct_0(X33),u1_struct_0(X32),k2_tops_2(u1_struct_0(X32),u1_struct_0(X33),X34)) = k2_struct_0(X32)
        | k2_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34) != k2_struct_0(X33)
        | ~ v2_funct_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
        | v2_struct_0(X33)
        | ~ l1_struct_0(X33)
        | ~ l1_struct_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).

cnf(c_0_44,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk1_0),X1)
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_46,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_50,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,X26,X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) != X27
      | ~ v2_funct_1(X28)
      | k2_tops_2(X26,X27,X28) = k2_funct_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_52,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X2)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1_0),X1)
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_27])])).

cnf(c_0_58,plain,
    ( v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))
    | ~ v4_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_37])])).

cnf(c_0_60,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_24])).

cnf(c_0_61,plain,
    ( v3_tops_2(X3,X1,X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_62,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_63,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ v2_funct_1(X11)
      | k2_funct_1(k2_funct_1(X11)) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

fof(c_0_64,plain,(
    ! [X10] :
      ( ( v1_relat_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X10) )
      & ( v1_funct_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X10) )
      & ( v2_funct_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_65,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3)) = k2_struct_0(X1)
    | v2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3) != k2_struct_0(X1)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_28]),c_0_53]),c_0_29])]),c_0_54])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk1_0),k2_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_36]),c_0_37])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_71,plain,
    ( v3_tops_2(X1,X2,X3)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != k2_struct_0(X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1) != u1_struct_0(X3)
    | ~ v5_pre_topc(k2_funct_1(X1),X3,X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) = k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_24]),c_0_28]),c_0_53]),c_0_29])]),c_0_54])).

cnf(c_0_76,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = k2_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_62]),c_0_28]),c_0_53]),c_0_29]),c_0_24])])).

cnf(c_0_77,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])])).

cnf(c_0_78,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_62]),c_0_28]),c_0_29]),c_0_24])])).

cnf(c_0_79,plain,
    ( v3_tops_2(k2_funct_1(X1),X2,X3)
    | k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1)) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1)) != k2_struct_0(X3)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1)) != u1_struct_0(X3)
    | ~ v5_pre_topc(k2_funct_1(X1),X2,X3)
    | ~ v5_pre_topc(X1,X3,X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(k2_funct_1(X1),u1_struct_0(X2),u1_struct_0(X3))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_62]),c_0_28]),c_0_53]),c_0_29]),c_0_24])])).

cnf(c_0_81,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = u1_struct_0(esk1_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_53])])).

cnf(c_0_83,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_84,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v5_pre_topc(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_77]),c_0_27]),c_0_26]),c_0_53]),c_0_29]),c_0_37])]),c_0_81]),c_0_82])).

cnf(c_0_85,plain,
    ( v5_pre_topc(k2_funct_1(X1),X2,X3)
    | k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1) != u1_struct_0(X2)
    | ~ v3_tops_2(X1,X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_62]),c_0_44])).

fof(c_0_86,plain,(
    ! [X21,X22,X23] :
      ( ( v1_funct_1(k2_funct_1(X23))
        | ~ v2_funct_1(X23)
        | k2_relset_1(X21,X22,X23) != X22
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( v1_funct_2(k2_funct_1(X23),X22,X21)
        | ~ v2_funct_1(X23)
        | k2_relset_1(X21,X22,X23) != X22
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( m1_subset_1(k2_funct_1(X23),k1_zfmisc_1(k2_zfmisc_1(X22,X21)))
        | ~ v2_funct_1(X23)
        | k2_relset_1(X21,X22,X23) != X22
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X21,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_87,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_24])])).

cnf(c_0_88,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_28]),c_0_53]),c_0_29]),c_0_24])])).

cnf(c_0_90,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_28]),c_0_53]),c_0_29]),c_0_24])])).

cnf(c_0_92,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_93,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_24])])).

cnf(c_0_94,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_95,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_24])]),c_0_38])).

cnf(c_0_96,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_39]),c_0_27])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_39]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:50:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.54/0.74  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.54/0.74  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.54/0.74  #
% 0.54/0.74  # Preprocessing time       : 0.029 s
% 0.54/0.74  # Presaturation interreduction done
% 0.54/0.74  
% 0.54/0.74  # Proof found!
% 0.54/0.74  # SZS status Theorem
% 0.54/0.74  # SZS output start CNFRefutation
% 0.54/0.74  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.54/0.74  fof(d5_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>((((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))&v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_2)).
% 0.54/0.74  fof(t70_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tops_2)).
% 0.54/0.74  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.54/0.74  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.54/0.74  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.54/0.74  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.54/0.74  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.54/0.74  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.54/0.74  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.54/0.74  fof(t62_tops_2, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 0.54/0.74  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 0.54/0.74  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 0.54/0.74  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.54/0.74  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.54/0.74  fof(c_0_15, plain, ![X18, X19, X20]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k1_relset_1(X18,X19,X20)=k1_relat_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.54/0.74  fof(c_0_16, plain, ![X29, X30, X31]:((((((k1_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31)=k2_struct_0(X29)|~v3_tops_2(X31,X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30)))))|~l1_pre_topc(X30)|~l1_pre_topc(X29))&(k2_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31)=k2_struct_0(X30)|~v3_tops_2(X31,X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30)))))|~l1_pre_topc(X30)|~l1_pre_topc(X29)))&(v2_funct_1(X31)|~v3_tops_2(X31,X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30)))))|~l1_pre_topc(X30)|~l1_pre_topc(X29)))&(v5_pre_topc(X31,X29,X30)|~v3_tops_2(X31,X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30)))))|~l1_pre_topc(X30)|~l1_pre_topc(X29)))&(v5_pre_topc(k2_tops_2(u1_struct_0(X29),u1_struct_0(X30),X31),X30,X29)|~v3_tops_2(X31,X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30)))))|~l1_pre_topc(X30)|~l1_pre_topc(X29)))&(k1_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31)!=k2_struct_0(X29)|k2_relset_1(u1_struct_0(X29),u1_struct_0(X30),X31)!=k2_struct_0(X30)|~v2_funct_1(X31)|~v5_pre_topc(X31,X29,X30)|~v5_pre_topc(k2_tops_2(u1_struct_0(X29),u1_struct_0(X30),X31),X30,X29)|v3_tops_2(X31,X29,X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X29),u1_struct_0(X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X30)))))|~l1_pre_topc(X30)|~l1_pre_topc(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).
% 0.54/0.74  fof(c_0_17, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)=>v3_tops_2(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)))))), inference(assume_negation,[status(cth)],[t70_tops_2])).
% 0.54/0.74  cnf(c_0_18, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.54/0.74  cnf(c_0_19, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.74  fof(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)&((~v2_struct_0(esk2_0)&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v3_tops_2(esk3_0,esk1_0,esk2_0)&~v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_17])])])])).
% 0.54/0.74  fof(c_0_21, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.54/0.74  fof(c_0_22, plain, ![X8, X9]:((~v4_relat_1(X9,X8)|r1_tarski(k1_relat_1(X9),X8)|~v1_relat_1(X9))&(~r1_tarski(k1_relat_1(X9),X8)|v4_relat_1(X9,X8)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.54/0.74  cnf(c_0_23, plain, (k2_struct_0(X1)=k1_relat_1(X2)|~v3_tops_2(X2,X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.54/0.74  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_25, negated_conjecture, (v3_tops_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.74  fof(c_0_31, plain, ![X24]:(~l1_struct_0(X24)|k2_struct_0(X24)=u1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.54/0.74  fof(c_0_32, plain, ![X25]:(~l1_pre_topc(X25)|l1_struct_0(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.54/0.74  fof(c_0_33, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.54/0.74  fof(c_0_34, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.54/0.74  cnf(c_0_35, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.54/0.74  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk3_0)=k2_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])])).
% 0.54/0.74  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_24])).
% 0.54/0.74  cnf(c_0_38, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.54/0.74  cnf(c_0_39, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.54/0.74  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.54/0.74  cnf(c_0_41, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.54/0.74  fof(c_0_42, plain, ![X15, X16, X17]:((v4_relat_1(X17,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(v5_relat_1(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.54/0.74  fof(c_0_43, plain, ![X32, X33, X34]:((k1_relset_1(u1_struct_0(X33),u1_struct_0(X32),k2_tops_2(u1_struct_0(X32),u1_struct_0(X33),X34))=k2_struct_0(X33)|(k2_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34)!=k2_struct_0(X33)|~v2_funct_1(X34))|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33)))))|(v2_struct_0(X33)|~l1_struct_0(X33))|~l1_struct_0(X32))&(k2_relset_1(u1_struct_0(X33),u1_struct_0(X32),k2_tops_2(u1_struct_0(X32),u1_struct_0(X33),X34))=k2_struct_0(X32)|(k2_relset_1(u1_struct_0(X32),u1_struct_0(X33),X34)!=k2_struct_0(X33)|~v2_funct_1(X34))|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33)))))|(v2_struct_0(X33)|~l1_struct_0(X33))|~l1_struct_0(X32))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_tops_2])])])])])).
% 0.54/0.74  cnf(c_0_44, plain, (v2_funct_1(X1)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.74  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_struct_0(esk1_0),X1)|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.54/0.74  cnf(c_0_46, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.54/0.74  cnf(c_0_47, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.54/0.74  cnf(c_0_48, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 0.54/0.74  cnf(c_0_49, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_35])).
% 0.54/0.74  cnf(c_0_50, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.54/0.74  fof(c_0_51, plain, ![X26, X27, X28]:(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|(k2_relset_1(X26,X27,X28)!=X27|~v2_funct_1(X28)|k2_tops_2(X26,X27,X28)=k2_funct_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.54/0.74  cnf(c_0_52, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X2)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.54/0.74  cnf(c_0_53, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])])).
% 0.54/0.74  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_55, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.54/0.74  cnf(c_0_56, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.54/0.74  cnf(c_0_57, negated_conjecture, (r1_tarski(u1_struct_0(esk1_0),X1)|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_27])])).
% 0.54/0.74  cnf(c_0_58, plain, (v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.54/0.74  cnf(c_0_59, negated_conjecture, (m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(X1))|~v4_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_36]), c_0_37])])).
% 0.54/0.74  cnf(c_0_60, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_50, c_0_24])).
% 0.54/0.74  cnf(c_0_61, plain, (v3_tops_2(X3,X1,X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v5_pre_topc(X3,X1,X2)|~v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.74  cnf(c_0_62, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.54/0.74  fof(c_0_63, plain, ![X11]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~v2_funct_1(X11)|k2_funct_1(k2_funct_1(X11))=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.54/0.74  fof(c_0_64, plain, ![X10]:(((v1_relat_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)|~v2_funct_1(X10)))&(v1_funct_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)|~v2_funct_1(X10))))&(v2_funct_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)|~v2_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.54/0.74  cnf(c_0_65, plain, (k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),X3))=k2_struct_0(X1)|v2_struct_0(X1)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3)!=k2_struct_0(X1)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~l1_struct_0(X1)|~l1_struct_0(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.54/0.74  cnf(c_0_66, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=k2_struct_0(esk1_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_28]), c_0_53]), c_0_29])]), c_0_54])).
% 0.54/0.74  cnf(c_0_67, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.54/0.74  cnf(c_0_68, negated_conjecture, (r1_tarski(u1_struct_0(esk1_0),k2_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_36]), c_0_37])])).
% 0.54/0.74  cnf(c_0_69, negated_conjecture, (m1_subset_1(k2_struct_0(esk1_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.54/0.74  cnf(c_0_70, negated_conjecture, (~v3_tops_2(k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0),esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.54/0.74  cnf(c_0_71, plain, (v3_tops_2(X1,X2,X3)|k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X2)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=k2_struct_0(X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1)!=u1_struct_0(X3)|~v5_pre_topc(k2_funct_1(X1),X3,X2)|~v5_pre_topc(X1,X2,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.54/0.74  cnf(c_0_72, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.54/0.74  cnf(c_0_73, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.54/0.74  cnf(c_0_74, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.54/0.74  cnf(c_0_75, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_24]), c_0_28]), c_0_53]), c_0_29])]), c_0_54])).
% 0.54/0.74  cnf(c_0_76, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=k2_struct_0(esk1_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_62]), c_0_28]), c_0_53]), c_0_29]), c_0_24])])).
% 0.54/0.74  cnf(c_0_77, negated_conjecture, (k2_struct_0(esk1_0)=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])])).
% 0.54/0.74  cnf(c_0_78, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_62]), c_0_28]), c_0_29]), c_0_24])])).
% 0.54/0.74  cnf(c_0_79, plain, (v3_tops_2(k2_funct_1(X1),X2,X3)|k1_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1))!=k2_struct_0(X2)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1))!=k2_struct_0(X3)|k2_relset_1(u1_struct_0(X2),u1_struct_0(X3),k2_funct_1(X1))!=u1_struct_0(X3)|~v5_pre_topc(k2_funct_1(X1),X2,X3)|~v5_pre_topc(X1,X3,X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(k2_funct_1(X1),u1_struct_0(X2),u1_struct_0(X3))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74])).
% 0.54/0.74  cnf(c_0_80, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_62]), c_0_28]), c_0_53]), c_0_29]), c_0_24])])).
% 0.54/0.74  cnf(c_0_81, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=u1_struct_0(esk1_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.54/0.74  cnf(c_0_82, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v3_tops_2(k2_funct_1(esk3_0),esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_53])])).
% 0.54/0.74  cnf(c_0_83, plain, (v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.74  cnf(c_0_84, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v5_pre_topc(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_77]), c_0_27]), c_0_26]), c_0_53]), c_0_29]), c_0_37])]), c_0_81]), c_0_82])).
% 0.54/0.74  cnf(c_0_85, plain, (v5_pre_topc(k2_funct_1(X1),X2,X3)|k2_relset_1(u1_struct_0(X3),u1_struct_0(X2),X1)!=u1_struct_0(X2)|~v3_tops_2(X1,X3,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_62]), c_0_44])).
% 0.54/0.74  fof(c_0_86, plain, ![X21, X22, X23]:(((v1_funct_1(k2_funct_1(X23))|(~v2_funct_1(X23)|k2_relset_1(X21,X22,X23)!=X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&(v1_funct_2(k2_funct_1(X23),X22,X21)|(~v2_funct_1(X23)|k2_relset_1(X21,X22,X23)!=X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))&(m1_subset_1(k2_funct_1(X23),k1_zfmisc_1(k2_zfmisc_1(X22,X21)))|(~v2_funct_1(X23)|k2_relset_1(X21,X22,X23)!=X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,X21,X22)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.54/0.74  cnf(c_0_87, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_24])])).
% 0.54/0.74  cnf(c_0_88, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.54/0.74  cnf(c_0_89, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_28]), c_0_53]), c_0_29]), c_0_24])])).
% 0.54/0.74  cnf(c_0_90, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.54/0.74  cnf(c_0_91, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_28]), c_0_53]), c_0_29]), c_0_24])])).
% 0.54/0.74  cnf(c_0_92, plain, (v5_pre_topc(X1,X2,X3)|~v3_tops_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.74  cnf(c_0_93, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_24])])).
% 0.54/0.74  cnf(c_0_94, plain, (k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)|~v3_tops_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.54/0.74  cnf(c_0_95, negated_conjecture, (~l1_struct_0(esk1_0)|~l1_struct_0(esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_24])]), c_0_38])).
% 0.54/0.74  cnf(c_0_96, negated_conjecture, (~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_39]), c_0_27])])).
% 0.54/0.74  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_39]), c_0_26])]), ['proof']).
% 0.54/0.74  # SZS output end CNFRefutation
% 0.54/0.74  # Proof object total steps             : 98
% 0.54/0.74  # Proof object clause steps            : 67
% 0.54/0.74  # Proof object formula steps           : 31
% 0.54/0.74  # Proof object conjectures             : 36
% 0.54/0.74  # Proof object clause conjectures      : 33
% 0.54/0.74  # Proof object formula conjectures     : 3
% 0.54/0.74  # Proof object initial clauses used    : 33
% 0.54/0.74  # Proof object initial formulas used   : 15
% 0.54/0.74  # Proof object generating inferences   : 31
% 0.54/0.74  # Proof object simplifying inferences  : 99
% 0.54/0.74  # Training examples: 0 positive, 0 negative
% 0.54/0.74  # Parsed axioms                        : 15
% 0.54/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.74  # Initial clauses                      : 37
% 0.54/0.74  # Removed in clause preprocessing      : 0
% 0.54/0.74  # Initial clauses in saturation        : 37
% 0.54/0.74  # Processed clauses                    : 2661
% 0.54/0.74  # ...of these trivial                  : 63
% 0.54/0.74  # ...subsumed                          : 1254
% 0.54/0.74  # ...remaining for further processing  : 1344
% 0.54/0.74  # Other redundant clauses eliminated   : 2
% 0.54/0.74  # Clauses deleted for lack of memory   : 0
% 0.54/0.74  # Backward-subsumed                    : 731
% 0.54/0.74  # Backward-rewritten                   : 191
% 0.54/0.74  # Generated clauses                    : 3839
% 0.54/0.74  # ...of the previous two non-trivial   : 3663
% 0.54/0.74  # Contextual simplify-reflections      : 512
% 0.54/0.74  # Paramodulations                      : 3837
% 0.54/0.74  # Factorizations                       : 0
% 0.54/0.74  # Equation resolutions                 : 2
% 0.54/0.74  # Propositional unsat checks           : 0
% 0.54/0.74  #    Propositional check models        : 0
% 0.54/0.74  #    Propositional check unsatisfiable : 0
% 0.54/0.74  #    Propositional clauses             : 0
% 0.54/0.74  #    Propositional clauses after purity: 0
% 0.54/0.74  #    Propositional unsat core size     : 0
% 0.54/0.74  #    Propositional preprocessing time  : 0.000
% 0.54/0.74  #    Propositional encoding time       : 0.000
% 0.54/0.74  #    Propositional solver time         : 0.000
% 0.54/0.74  #    Success case prop preproc time    : 0.000
% 0.54/0.74  #    Success case prop encoding time   : 0.000
% 0.54/0.74  #    Success case prop solver time     : 0.000
% 0.54/0.74  # Current number of processed clauses  : 384
% 0.54/0.74  #    Positive orientable unit clauses  : 37
% 0.54/0.74  #    Positive unorientable unit clauses: 0
% 0.54/0.74  #    Negative unit clauses             : 3
% 0.54/0.74  #    Non-unit-clauses                  : 344
% 0.54/0.74  # Current number of unprocessed clauses: 902
% 0.54/0.74  # ...number of literals in the above   : 9436
% 0.54/0.74  # Current number of archived formulas  : 0
% 0.54/0.74  # Current number of archived clauses   : 958
% 0.54/0.74  # Clause-clause subsumption calls (NU) : 219218
% 0.54/0.74  # Rec. Clause-clause subsumption calls : 18292
% 0.54/0.74  # Non-unit clause-clause subsumptions  : 2491
% 0.54/0.74  # Unit Clause-clause subsumption calls : 3030
% 0.54/0.74  # Rewrite failures with RHS unbound    : 0
% 0.54/0.74  # BW rewrite match attempts            : 40
% 0.54/0.74  # BW rewrite match successes           : 3
% 0.54/0.74  # Condensation attempts                : 0
% 0.54/0.74  # Condensation successes               : 0
% 0.54/0.74  # Termbank termtop insertions          : 188773
% 0.54/0.74  
% 0.54/0.74  # -------------------------------------------------
% 0.54/0.74  # User time                : 0.401 s
% 0.54/0.74  # System time              : 0.005 s
% 0.54/0.74  # Total time               : 0.405 s
% 0.54/0.74  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
