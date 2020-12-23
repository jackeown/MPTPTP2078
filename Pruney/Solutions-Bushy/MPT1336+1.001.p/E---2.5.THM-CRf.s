%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1336+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:09 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 233 expanded)
%              Number of clauses        :   50 (  85 expanded)
%              Number of leaves         :   12 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  390 (1820 expanded)
%              Number of equality atoms :   64 ( 198 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                 => ( ( v5_pre_topc(X3,X1,X2)
                      & v1_tops_2(X4,X2) )
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                       => ( X5 = k9_relat_1(k3_funct_3(X3),X4)
                         => v1_tops_2(X5,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_2)).

fof(t55_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => ( v5_pre_topc(X3,X1,X2)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( v3_pre_topc(X4,X2)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(t24_funct_3,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(k3_funct_3(X2)))
       => k1_funct_1(k3_funct_3(X2),X1) = k10_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_3)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(dt_k3_funct_3,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k3_funct_3(X1))
        & v1_funct_1(k3_funct_3(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_3)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( ( v5_pre_topc(X3,X1,X2)
                        & v1_tops_2(X4,X2) )
                     => ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                         => ( X5 = k9_relat_1(k3_funct_3(X3),X4)
                           => v1_tops_2(X5,X1) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_tops_2])).

fof(c_0_13,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ v5_pre_topc(X39,X37,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ v3_pre_topc(X40,X38)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,X40),X37)
        | k2_struct_0(X38) = k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk5_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X38)))
        | v5_pre_topc(X39,X37,X38)
        | k2_struct_0(X38) = k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( v3_pre_topc(esk5_3(X37,X38,X39),X38)
        | v5_pre_topc(X39,X37,X38)
        | k2_struct_0(X38) = k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,esk5_3(X37,X38,X39)),X37)
        | v5_pre_topc(X39,X37,X38)
        | k2_struct_0(X38) = k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( ~ v5_pre_topc(X39,X37,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ v3_pre_topc(X40,X38)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,X40),X37)
        | k2_struct_0(X37) != k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( m1_subset_1(esk5_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X38)))
        | v5_pre_topc(X39,X37,X38)
        | k2_struct_0(X37) != k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( v3_pre_topc(esk5_3(X37,X38,X39),X38)
        | v5_pre_topc(X39,X37,X38)
        | k2_struct_0(X37) != k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X37),u1_struct_0(X38),X39,esk5_3(X37,X38,X39)),X37)
        | v5_pre_topc(X39,X37,X38)
        | k2_struct_0(X37) != k1_xboole_0
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
        | ~ l1_pre_topc(X38)
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

fof(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & l1_pre_topc(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0))))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0))))
    & v5_pre_topc(esk8_0,esk6_0,esk7_0)
    & v1_tops_2(esk9_0,esk7_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0))))
    & esk10_0 = k9_relat_1(k3_funct_3(esk8_0),esk9_0)
    & ~ v1_tops_2(esk10_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ r2_hidden(X32,k1_relat_1(k3_funct_3(X33)))
      | k1_funct_1(k3_funct_3(X33),X32) = k10_relat_1(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_funct_3])])).

fof(c_0_16,plain,(
    ! [X9,X10,X11,X12,X14,X15,X16,X17,X19] :
      ( ( r2_hidden(esk1_4(X9,X10,X11,X12),k1_relat_1(X9))
        | ~ r2_hidden(X12,X11)
        | X11 != k9_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk1_4(X9,X10,X11,X12),X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k9_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( X12 = k1_funct_1(X9,esk1_4(X9,X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | X11 != k9_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(X15,k1_relat_1(X9))
        | ~ r2_hidden(X15,X10)
        | X14 != k1_funct_1(X9,X15)
        | r2_hidden(X14,X11)
        | X11 != k9_relat_1(X9,X10)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(esk2_3(X9,X16,X17),X17)
        | ~ r2_hidden(X19,k1_relat_1(X9))
        | ~ r2_hidden(X19,X16)
        | esk2_3(X9,X16,X17) != k1_funct_1(X9,X19)
        | X17 = k9_relat_1(X9,X16)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk3_3(X9,X16,X17),k1_relat_1(X9))
        | r2_hidden(esk2_3(X9,X16,X17),X17)
        | X17 = k9_relat_1(X9,X16)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk3_3(X9,X16,X17),X16)
        | r2_hidden(esk2_3(X9,X16,X17),X17)
        | X17 = k9_relat_1(X9,X16)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk2_3(X9,X16,X17) = k1_funct_1(X9,esk3_3(X9,X16,X17))
        | r2_hidden(esk2_3(X9,X16,X17),X17)
        | X17 = k9_relat_1(X9,X16)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_17,plain,(
    ! [X25] :
      ( ( v1_relat_1(k3_funct_3(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v1_funct_1(k3_funct_3(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_funct_3])])])).

cnf(c_0_18,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | k2_struct_0(X3) = k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk6_0),u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k8_relset_1(X28,X29,X30,X31) = k10_relat_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_26,plain,
    ( k1_funct_1(k3_funct_3(X1),X2) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(k3_funct_3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( v1_relat_1(k3_funct_3(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( v1_funct_1(k3_funct_3(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_30,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_31,plain,(
    ! [X34,X35,X36] :
      ( ~ r2_hidden(X34,X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(X36))
      | m1_subset_1(X34,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_32,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk7_0),esk8_0,X1),esk6_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_33,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( X1 = k1_funct_1(X2,esk1_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( k1_funct_1(k3_funct_3(X1),esk1_4(k3_funct_3(X1),X2,X3,X4)) = k10_relat_1(X1,esk1_4(k3_funct_3(X1),X2,X3,X4))
    | X3 != k9_relat_1(k3_funct_3(X1),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(k10_relat_1(esk8_0,X1),esk6_0)
    | ~ v3_pre_topc(X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19])])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,esk1_4(k3_funct_3(X1),X2,X3,X4)) = X4
    | X3 != k9_relat_1(k3_funct_3(X1),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0)))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != k9_relat_1(k3_funct_3(esk8_0),X3)
    | ~ v3_pre_topc(esk1_4(k3_funct_3(esk8_0),X3,X2,X1),esk7_0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(esk1_4(k3_funct_3(esk8_0),X3,X2,X1),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24]),c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk1_4(X1,esk9_0,X2,X3),k1_zfmisc_1(u1_struct_0(esk7_0)))
    | X2 != k9_relat_1(X1,esk9_0)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( esk10_0 = k9_relat_1(k3_funct_3(esk8_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_47,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_tops_2(X22,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ r2_hidden(X23,X22)
        | v3_pre_topc(X23,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(esk4_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | v1_tops_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(esk4_2(X21,X22),X22)
        | v1_tops_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) )
      & ( ~ v3_pre_topc(esk4_2(X21,X22),X21)
        | v1_tops_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X21))))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

cnf(c_0_48,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != esk10_0
    | ~ v3_pre_topc(esk1_4(k3_funct_3(esk8_0),esk9_0,X2,X1),esk7_0)
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_1(k3_funct_3(esk8_0))
    | ~ v1_relat_1(k3_funct_3(esk8_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_49,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != esk10_0
    | ~ v3_pre_topc(esk1_4(k3_funct_3(esk8_0),esk9_0,X2,X1),esk7_0)
    | ~ r2_hidden(X1,X2)
    | ~ v1_relat_1(k3_funct_3(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_29]),c_0_24]),c_0_41])])).

cnf(c_0_51,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v1_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_49,c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( v1_tops_2(esk9_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != esk10_0
    | ~ v3_pre_topc(esk1_4(k3_funct_3(esk8_0),esk9_0,X2,X1),esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_24]),c_0_41])])).

cnf(c_0_54,negated_conjecture,
    ( v3_pre_topc(X1,esk7_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_52]),c_0_22])])).

cnf(c_0_55,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != esk10_0
    | ~ r2_hidden(esk1_4(k3_funct_3(esk8_0),esk9_0,X2,X1),esk9_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_56,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != esk10_0
    | ~ r2_hidden(X1,X2)
    | ~ v1_funct_1(k3_funct_3(esk8_0))
    | ~ v1_relat_1(k3_funct_3(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_43]),c_0_46])])).

cnf(c_0_57,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != esk10_0
    | ~ r2_hidden(X1,X2)
    | ~ v1_relat_1(k3_funct_3(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_29]),c_0_24]),c_0_41])])).

cnf(c_0_58,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_tops_2(esk10_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(X1,esk6_0)
    | X2 != esk10_0
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_28]),c_0_24]),c_0_41])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk4_2(esk6_0,esk10_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_23])]),c_0_60])).

fof(c_0_63,plain,(
    ! [X27] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ v1_xboole_0(k2_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_64,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_65,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0
    | v3_pre_topc(esk4_2(esk6_0,esk10_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k2_struct_0(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_23]),c_0_59])]),c_0_60])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_70,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | l1_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_71,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),c_0_69])).

cnf(c_0_72,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_22])]),
    [proof]).

%------------------------------------------------------------------------------
