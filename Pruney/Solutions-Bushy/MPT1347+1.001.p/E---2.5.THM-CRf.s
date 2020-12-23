%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1347+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:10 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  142 (23376 expanded)
%              Number of clauses        :  101 (7865 expanded)
%              Number of leaves         :   20 (5737 expanded)
%              Depth                    :   20
%              Number of atoms          :  538 (297744 expanded)
%              Number of equality atoms :   86 (52202 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   46 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t72_tops_2,conjecture,(
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
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v4_pre_topc(X4,X1)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(t154_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(t152_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => r1_tarski(k10_relat_1(X2,k9_relat_1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_20,negated_conjecture,(
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
                <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( v4_pre_topc(X4,X1)
                        <=> v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t72_tops_2])).

fof(c_0_21,plain,(
    ! [X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_relset_1(X37,X38,X39) = k2_relat_1(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_22,negated_conjecture,(
    ! [X62] :
      ( l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & l1_pre_topc(esk3_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
      & ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk2_0)
        | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk3_0)
        | ~ v2_funct_1(esk4_0)
        | ~ v3_tops_2(esk4_0,esk2_0,esk3_0) )
      & ( ~ v4_pre_topc(esk5_0,esk2_0)
        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)
        | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk2_0)
        | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk3_0)
        | ~ v2_funct_1(esk4_0)
        | ~ v3_tops_2(esk4_0,esk2_0,esk3_0) )
      & ( v4_pre_topc(esk5_0,esk2_0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)
        | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk2_0)
        | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk3_0)
        | ~ v2_funct_1(esk4_0)
        | ~ v3_tops_2(esk4_0,esk2_0,esk3_0) )
      & ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk2_0)
        | v3_tops_2(esk4_0,esk2_0,esk3_0) )
      & ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0)
        | v3_tops_2(esk4_0,esk2_0,esk3_0) )
      & ( v2_funct_1(esk4_0)
        | v3_tops_2(esk4_0,esk2_0,esk3_0) )
      & ( ~ v4_pre_topc(X62,esk2_0)
        | v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X62),esk3_0)
        | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | v3_tops_2(esk4_0,esk2_0,esk3_0) )
      & ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X62),esk3_0)
        | v4_pre_topc(X62,esk2_0)
        | ~ m1_subset_1(X62,k1_zfmisc_1(u1_struct_0(esk2_0)))
        | v3_tops_2(esk4_0,esk2_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])])).

fof(c_0_23,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_24,plain,(
    ! [X40,X41,X42,X43] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k7_relset_1(X40,X41,X42,X43) = k9_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_25,plain,(
    ! [X50,X51] :
      ( ~ v1_relat_1(X51)
      | ~ v1_funct_1(X51)
      | ~ r1_tarski(X50,k2_relat_1(X51))
      | k9_relat_1(X51,k10_relat_1(X51,X50)) = X50 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_26,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_relat_1(esk4_0) = k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k9_relat_1(esk4_0,X1) = k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

fof(c_0_35,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_36,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | l1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_37,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ v5_pre_topc(X12,X10,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ v4_pre_topc(X13,X11)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12,X13),X10)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_3(X10,X11,X12),k1_zfmisc_1(u1_struct_0(X11)))
        | v5_pre_topc(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( v4_pre_topc(esk1_3(X10,X11,X12),X11)
        | v5_pre_topc(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X10),u1_struct_0(X11),X12,esk1_3(X10,X11,X12)),X10)
        | v5_pre_topc(X12,X10,X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_pre_topc(X11)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_38,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k10_relat_1(esk4_0,X1)) = X1
    | ~ r1_tarski(X1,k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X56,X57] :
      ( ( ~ m1_subset_1(X56,k1_zfmisc_1(X57))
        | r1_tarski(X56,X57) )
      & ( ~ r1_tarski(X56,X57)
        | m1_subset_1(X56,k1_zfmisc_1(X57)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_43,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_47,plain,(
    ! [X29,X30,X31,X32] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | m1_subset_1(k8_relset_1(X29,X30,X31,X32),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

fof(c_0_48,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k8_relset_1(X44,X45,X46,X47) = k10_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_49,plain,(
    ! [X22,X23,X24] :
      ( ( v1_funct_1(k2_tops_2(X22,X23,X24))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(k2_tops_2(X22,X23,X24),X23,X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(k2_tops_2(X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X23,X22)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

fof(c_0_50,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_funct_1(X18)
      | ~ v1_funct_2(X18,X16,X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k2_relset_1(X16,X17,X18) != X17
      | ~ v2_funct_1(X18)
      | k2_tops_2(X16,X17,X18) = k2_funct_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_51,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k10_relat_1(esk4_0,X1)) = X1
    | v3_tops_2(esk4_0,esk2_0,esk3_0)
    | ~ r1_tarski(X1,k2_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_60,plain,(
    ! [X19,X20,X21] :
      ( ( k1_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21) = k2_struct_0(X19)
        | ~ v3_tops_2(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21) = k2_struct_0(X20)
        | ~ v3_tops_2(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( v2_funct_1(X21)
        | ~ v3_tops_2(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( v5_pre_topc(X21,X19,X20)
        | ~ v3_tops_2(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( v5_pre_topc(k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21),X20,X19)
        | ~ v3_tops_2(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( k1_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21) != k2_struct_0(X19)
        | k2_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21) != k2_struct_0(X20)
        | ~ v2_funct_1(X21)
        | ~ v5_pre_topc(X21,X19,X20)
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X19),u1_struct_0(X20),X21),X20,X19)
        | v3_tops_2(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tops_2])])])])).

cnf(c_0_61,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k10_relat_1(esk4_0,X1)) = X1
    | v3_tops_2(esk4_0,esk2_0,esk3_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_45])])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | r1_tarski(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) = k10_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_65,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_66,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_32]),c_0_27])])).

cnf(c_0_68,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_69,plain,
    ( v1_funct_1(k2_tops_2(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_70,plain,(
    ! [X54,X55] :
      ( ~ v1_relat_1(X55)
      | ~ v1_funct_1(X55)
      | ~ v2_funct_1(X55)
      | k9_relat_1(X55,X54) = k10_relat_1(k2_funct_1(X55),X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).

cnf(c_0_71,negated_conjecture,
    ( k2_funct_1(esk4_0) = k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0)
    | k2_struct_0(esk3_0) != u1_struct_0(esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_39]),c_0_44]),c_0_32]),c_0_27])]),c_0_59])).

cnf(c_0_72,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk2_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_74,negated_conjecture,
    ( v4_pre_topc(X1,esk2_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,k10_relat_1(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0))) = esk1_3(esk2_0,esk3_0,esk4_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k10_relat_1(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_77,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_78,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(k10_relat_1(esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_64]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_79,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),X1) = k10_relat_1(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_44]),c_0_32]),c_0_27])])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_1(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_44]),c_0_32]),c_0_27])])).

cnf(c_0_82,plain,
    ( k9_relat_1(X1,X2) = k10_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( k2_funct_1(esk4_0) = k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_52]),c_0_45])])).

cnf(c_0_84,negated_conjecture,
    ( v3_tops_2(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])]),c_0_59]),c_0_39])).

cnf(c_0_85,negated_conjecture,
    ( v3_tops_2(esk4_0,esk2_0,esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])]),c_0_77]),c_0_78])).

fof(c_0_86,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k1_relset_1(X34,X35,X36) = k1_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_87,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)
    | ~ v4_pre_topc(k10_relat_1(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_79]),c_0_80]),c_0_81]),c_0_46]),c_0_45]),c_0_67])])).

cnf(c_0_88,negated_conjecture,
    ( k10_relat_1(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),X1) = k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)
    | v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_34]),c_0_32]),c_0_33])]),c_0_59])).

cnf(c_0_89,negated_conjecture,
    ( v3_tops_2(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

fof(c_0_90,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X49)
      | ~ r1_tarski(X48,k1_relat_1(X49))
      | r1_tarski(X48,k10_relat_1(X49,k9_relat_1(X49,X48))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_91,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk3_0)
    | v3_tops_2(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_93,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk2_0)
    | v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_80]),c_0_81]),c_0_46]),c_0_45]),c_0_67])])).

cnf(c_0_94,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0)
    | m1_subset_1(esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_80]),c_0_81]),c_0_46]),c_0_45]),c_0_67])])).

cnf(c_0_95,negated_conjecture,
    ( v3_tops_2(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk3_0,esk2_0,k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0))),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_96,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_27])).

cnf(c_0_98,plain,
    ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_99,negated_conjecture,
    ( v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_89]),c_0_95])).

cnf(c_0_100,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_101,plain,
    ( v2_funct_1(X1)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)))
    | ~ r1_tarski(X1,k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_33])]),c_0_34])).

cnf(c_0_103,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk3_0)
    | ~ v2_funct_1(esk4_0)
    | ~ v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_105,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_99]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_106,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_99]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

fof(c_0_107,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X53)
      | ~ v1_funct_1(X53)
      | ~ v2_funct_1(X53)
      | r1_tarski(k10_relat_1(X53,k9_relat_1(X53,X52)),X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t152_funct_1])])).

cnf(c_0_108,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v3_tops_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_109,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k7_relset_1(X25,X26,X27,X28),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)))
    | ~ r1_tarski(X1,k2_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_99])]),c_0_105]),c_0_103]),c_0_106])])).

cnf(c_0_112,plain,
    ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_113,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_114,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_99]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_115,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk2_0)
    | v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk3_0)
    | ~ v2_funct_1(esk4_0)
    | ~ v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_116,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

fof(c_0_117,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(X1,k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_52]),c_0_46])])).

cnf(c_0_119,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)),X1)
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_34]),c_0_32]),c_0_33])])).

cnf(c_0_121,negated_conjecture,
    ( k2_funct_1(esk4_0) = k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)
    | k2_struct_0(esk3_0) != u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_105]),c_0_106]),c_0_44]),c_0_32]),c_0_27])])).

cnf(c_0_122,negated_conjecture,
    ( ~ v4_pre_topc(esk5_0,esk2_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk3_0)
    | ~ v2_funct_1(esk4_0)
    | ~ v3_tops_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_123,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_64]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_124,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)
    | v4_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_99])]),c_0_105]),c_0_103]),c_0_106])])).

cnf(c_0_125,negated_conjecture,
    ( m1_subset_1(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_116,c_0_27])).

cnf(c_0_126,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(esk5_0,k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_106])])).

cnf(c_0_129,plain,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3),X2,X1)
    | ~ v3_tops_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_130,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk4_0),X1) = k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1)
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_34]),c_0_32]),c_0_33])])).

cnf(c_0_131,negated_conjecture,
    ( k2_funct_1(esk4_0) = k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_52]),c_0_45])])).

cnf(c_0_132,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk3_0)
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) != k2_struct_0(esk2_0)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)
    | ~ v4_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_99])]),c_0_106])])).

cnf(c_0_133,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0)),esk2_0)
    | v4_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125])])).

cnf(c_0_134,negated_conjecture,
    ( k10_relat_1(esk4_0,k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_127]),c_0_128])])).

cnf(c_0_135,negated_conjecture,
    ( v5_pre_topc(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_99]),c_0_44]),c_0_32]),c_0_45]),c_0_46]),c_0_27])])).

cnf(c_0_136,negated_conjecture,
    ( k10_relat_1(k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0),X1) = k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_106])]),c_0_131])).

cnf(c_0_137,negated_conjecture,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0)
    | ~ v4_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_105])]),c_0_103])])).

cnf(c_0_138,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_133,c_0_134])])).

cnf(c_0_139,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk3_0)
    | ~ v4_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_135]),c_0_79]),c_0_136]),c_0_80]),c_0_81]),c_0_46]),c_0_45]),c_0_67])])).

cnf(c_0_140,negated_conjecture,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_138])])).

cnf(c_0_141,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_138]),c_0_111])]),c_0_140]),
    [proof]).

%------------------------------------------------------------------------------
