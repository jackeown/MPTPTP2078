%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  165 (26813209 expanded)
%              Number of clauses        :  140 (9230760 expanded)
%              Number of leaves         :   12 (6709839 expanded)
%              Depth                    :   45
%              Number of atoms          :  573 (208140806 expanded)
%              Number of equality atoms :  155 (23183362 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   27 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,u1_struct_0(X2))
                     => X4 = k1_funct_1(X3,X4) ) )
               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t8_grfunc_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( r1_tarski(X1,X2)
          <=> ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_grfunc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t95_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,u1_struct_0(X2))
               => k1_funct_1(k4_tmap_1(X1,X2),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,u1_struct_0(X2))
                       => X4 = k1_funct_1(X3,X4) ) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t96_tmap_1])).

fof(c_0_13,plain,(
    ! [X28,X29] :
      ( ( v1_funct_1(k4_tmap_1(X28,X29))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( v1_funct_2(k4_tmap_1(X28,X29),u1_struct_0(X29),u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) )
      & ( m1_subset_1(k4_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X28))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_pre_topc(X29,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_14,negated_conjecture,(
    ! [X38] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X38,u1_struct_0(esk2_0))
        | ~ r2_hidden(X38,u1_struct_0(esk3_0))
        | X38 = k1_funct_1(esk4_0,X38) )
      & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

fof(c_0_15,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v1_funct_2(X19,X17,X18)
        | X17 = k1_relset_1(X17,X18,X19)
        | X18 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X17 != k1_relset_1(X17,X18,X19)
        | v1_funct_2(X19,X17,X18)
        | X18 = k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_2(X19,X17,X18)
        | X17 = k1_relset_1(X17,X18,X19)
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X17 != k1_relset_1(X17,X18,X19)
        | v1_funct_2(X19,X17,X18)
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_2(X19,X17,X18)
        | X19 = k1_xboole_0
        | X17 = k1_xboole_0
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( X19 != k1_xboole_0
        | v1_funct_2(X19,X17,X18)
        | X17 = k1_xboole_0
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_23,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

fof(c_0_26,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_27,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_28,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | m1_subset_1(u1_struct_0(X31),k1_zfmisc_1(u1_struct_0(X30))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] :
      ( ( r1_tarski(k1_relat_1(X24),k1_relat_1(X25))
        | ~ r1_tarski(X24,X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(X26,k1_relat_1(X24))
        | k1_funct_1(X24,X26) = k1_funct_1(X25,X26)
        | ~ r1_tarski(X24,X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( r2_hidden(esk1_2(X24,X25),k1_relat_1(X24))
        | ~ r1_tarski(k1_relat_1(X24),k1_relat_1(X25))
        | r1_tarski(X24,X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( k1_funct_1(X24,esk1_2(X24,X25)) != k1_funct_1(X25,esk1_2(X24,X25))
        | ~ r1_tarski(k1_relat_1(X24),k1_relat_1(X25))
        | r1_tarski(X24,X25)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_32,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_37,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X7,X8,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X9))
      | m1_subset_1(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_24])])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_35]),c_0_36])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_17]),c_0_18])])).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(esk3_0))
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(u1_struct_0(esk3_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_44]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_35]),c_0_34])])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_45])).

fof(c_0_53,plain,(
    ! [X32,X33,X34] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ m1_pre_topc(X33,X32)
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | ~ r2_hidden(X34,u1_struct_0(X33))
      | k1_funct_1(k4_tmap_1(X32,X33),X34) = X34 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,X1),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( X1 = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X2)
    | k1_funct_1(X1,esk1_2(X1,X2)) != k1_funct_1(X2,esk1_2(X1,X2))
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_55]),c_0_17])]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_55]),c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk3_0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_66,plain,
    ( k1_funct_1(X2,X1) = k1_funct_1(X3,X1)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r1_tarski(X2,X3)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_50]),c_0_42]),c_0_51]),c_0_43])]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(u1_struct_0(esk3_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_52]),c_0_50]),c_0_51])])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1) = k1_funct_1(X2,X1)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(k4_tmap_1(esk2_0,esk3_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_41]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))
    | r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1) = k1_funct_1(esk4_0,X1)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_50]),c_0_51])])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_49]),c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_77,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_74]),c_0_42]),c_0_50]),c_0_43]),c_0_51])])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(k1_relat_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_52]),c_0_50]),c_0_51])])).

cnf(c_0_79,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_41]),c_0_78])).

fof(c_0_81,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r2_funct_2(X20,X21,X22,X23)
        | X22 = X23
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X22 != X23
        | r2_funct_2(X20,X21,X22,X23)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
        | ~ v1_funct_1(X23)
        | ~ v1_funct_2(X23,X20,X21)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_83,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_84,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_87,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_88,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_50]),c_0_36]),c_0_35])])).

cnf(c_0_89,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_35,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_88])).

cnf(c_0_93,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92])])).

cnf(c_0_95,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_88])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_94])).

cnf(c_0_103,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_94])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,X1),X2) = X2
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X2,k1_xboole_0)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_88]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_105,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk4_0,X1),k1_xboole_0)
    | r1_tarski(esk4_0,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_101]),c_0_50]),c_0_51])])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_102]),c_0_103])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_88]),c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1) = X1
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_94]),c_0_17])]),c_0_59]),c_0_105])).

cnf(c_0_110,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_42]),c_0_43]),c_0_52])])).

cnf(c_0_111,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | esk4_0 = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_94])).

cnf(c_0_112,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))
    | r1_tarski(X1,esk4_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_101]),c_0_50]),c_0_51])])).

cnf(c_0_113,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_101]),c_0_50]),c_0_51])])).

cnf(c_0_116,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_107]),c_0_42]),c_0_43]),c_0_52])])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_113]),c_0_42]),c_0_50]),c_0_43]),c_0_51])]),c_0_114])).

cnf(c_0_118,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_relat_1(esk4_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_52]),c_0_50]),c_0_51])])).

cnf(c_0_119,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_101]),c_0_50]),c_0_51])])).

cnf(c_0_122,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_107]),c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | ~ r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_119]),c_0_50]),c_0_42]),c_0_51]),c_0_43])]),c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_52]),c_0_50]),c_0_51])])).

cnf(c_0_125,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_107]),c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_88])).

cnf(c_0_128,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = k1_xboole_0
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_98]),c_0_99])])).

cnf(c_0_130,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_131,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_127,c_0_129])).

cnf(c_0_132,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_86]),c_0_50]),c_0_92]),c_0_91])])).

cnf(c_0_133,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_131,c_0_132])).

cnf(c_0_134,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_132])).

cnf(c_0_135,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_98,c_0_129])).

cnf(c_0_137,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_86]),c_0_134]),c_0_135])]),c_0_136])).

cnf(c_0_138,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_98,c_0_137])).

cnf(c_0_139,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_99,c_0_137])).

cnf(c_0_140,negated_conjecture,
    ( k1_relat_1(k4_tmap_1(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_138]),c_0_139])])).

cnf(c_0_141,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_132]),c_0_137])).

cnf(c_0_142,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_135,c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( m1_subset_1(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_100,c_0_137])).

cnf(c_0_144,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,X1) = X1
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_132])).

cnf(c_0_145,negated_conjecture,
    ( r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),X1),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_140]),c_0_42]),c_0_43])])).

cnf(c_0_146,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_141]),c_0_142])])).

cnf(c_0_147,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_132])).

cnf(c_0_148,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1) = X1
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_137]),c_0_17])]),c_0_59]),c_0_143])).

cnf(c_0_149,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,X1) = X1
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_144,c_0_137])).

cnf(c_0_150,negated_conjecture,
    ( r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_134]),c_0_147]),c_0_52])])).

cnf(c_0_151,negated_conjecture,
    ( r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))
    | r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_140]),c_0_42]),c_0_43])])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)
    | k1_funct_1(X1,esk1_2(k4_tmap_1(esk2_0,esk3_0),X1)) != esk1_2(k4_tmap_1(esk2_0,esk3_0),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_148]),c_0_42]),c_0_43]),c_0_140])]),c_0_145])).

cnf(c_0_153,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)) = esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)
    | r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_154,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_146]),c_0_134]),c_0_147]),c_0_52])])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_134]),c_0_147]),c_0_146]),c_0_52])])).

cnf(c_0_156,negated_conjecture,
    ( r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))
    | k1_funct_1(X1,esk1_2(X1,k4_tmap_1(esk2_0,esk3_0))) != esk1_2(X1,k4_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_148]),c_0_42]),c_0_43]),c_0_140])])).

cnf(c_0_157,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))) = esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))
    | r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_149,c_0_154])).

cnf(c_0_158,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_127,c_0_132])).

cnf(c_0_159,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_155])).

cnf(c_0_160,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_154]),c_0_134]),c_0_147]),c_0_146]),c_0_52])]),c_0_157])).

cnf(c_0_161,negated_conjecture,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_158,c_0_137])).

cnf(c_0_162,negated_conjecture,
    ( k4_tmap_1(esk2_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_160])])).

cnf(c_0_163,negated_conjecture,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_161,c_0_162])).

cnf(c_0_164,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_86]),c_0_134]),c_0_142]),c_0_141])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.030 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.19/0.40  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.19/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.40  fof(t8_grfunc_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,X2)<=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_grfunc_1)).
% 0.19/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.40  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.19/0.40  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.19/0.40  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.19/0.40  fof(c_0_13, plain, ![X28, X29]:(((v1_funct_1(k4_tmap_1(X28,X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28)))&(v1_funct_2(k4_tmap_1(X28,X29),u1_struct_0(X29),u1_struct_0(X28))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28))))&(m1_subset_1(k4_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X28))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_pre_topc(X29,X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.19/0.40  fof(c_0_14, negated_conjecture, ![X38]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X38,u1_struct_0(esk2_0))|(~r2_hidden(X38,u1_struct_0(esk3_0))|X38=k1_funct_1(esk4_0,X38)))&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 0.19/0.40  fof(c_0_15, plain, ![X17, X18, X19]:((((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X18=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&((~v1_funct_2(X19,X17,X18)|X17=k1_relset_1(X17,X18,X19)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X17!=k1_relset_1(X17,X18,X19)|v1_funct_2(X19,X17,X18)|X17!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&((~v1_funct_2(X19,X17,X18)|X19=k1_xboole_0|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(X19!=k1_xboole_0|v1_funct_2(X19,X17,X18)|X17=k1_xboole_0|X18!=k1_xboole_0|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.40  cnf(c_0_16, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_21, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  fof(c_0_22, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k1_relset_1(X14,X15,X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.40  cnf(c_0_23, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_24, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.40  cnf(c_0_25, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.40  fof(c_0_26, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.40  fof(c_0_27, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.40  fof(c_0_28, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|m1_subset_1(u1_struct_0(X31),k1_zfmisc_1(u1_struct_0(X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.40  fof(c_0_29, plain, ![X24, X25, X26]:(((r1_tarski(k1_relat_1(X24),k1_relat_1(X25))|~r1_tarski(X24,X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(~r2_hidden(X26,k1_relat_1(X24))|k1_funct_1(X24,X26)=k1_funct_1(X25,X26)|~r1_tarski(X24,X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))|(~v1_relat_1(X24)|~v1_funct_1(X24))))&((r2_hidden(esk1_2(X24,X25),k1_relat_1(X24))|~r1_tarski(k1_relat_1(X24),k1_relat_1(X25))|r1_tarski(X24,X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(k1_funct_1(X24,esk1_2(X24,X25))!=k1_funct_1(X25,esk1_2(X24,X25))|~r1_tarski(k1_relat_1(X24),k1_relat_1(X25))|r1_tarski(X24,X25)|(~v1_relat_1(X25)|~v1_funct_1(X25))|(~v1_relat_1(X24)|~v1_funct_1(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_grfunc_1])])])])])).
% 0.19/0.40  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.40  cnf(c_0_32, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.40  cnf(c_0_33, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.40  cnf(c_0_34, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.40  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  fof(c_0_37, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.40  fof(c_0_38, plain, ![X7, X8, X9]:(~r2_hidden(X7,X8)|~m1_subset_1(X8,k1_zfmisc_1(X9))|m1_subset_1(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.40  cnf(c_0_39, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.40  cnf(c_0_40, plain, (r2_hidden(esk1_2(X1,X2),k1_relat_1(X1))|r1_tarski(X1,X2)|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (k1_relat_1(k4_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_24])])).
% 0.19/0.40  cnf(c_0_42, negated_conjecture, (v1_funct_1(k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.40  cnf(c_0_43, negated_conjecture, (v1_relat_1(k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_24]), c_0_34])])).
% 0.19/0.40  cnf(c_0_44, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0)=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_35]), c_0_36])])).
% 0.19/0.40  cnf(c_0_45, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_46, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_17]), c_0_18])])).
% 0.19/0.40  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),X1),u1_struct_0(esk3_0))|r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(u1_struct_0(esk3_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_44]), c_0_35])])).
% 0.19/0.40  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_35]), c_0_34])])).
% 0.19/0.40  cnf(c_0_52, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_45])).
% 0.19/0.40  fof(c_0_53, plain, ![X32, X33, X34]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~m1_pre_topc(X33,X32)|(~m1_subset_1(X34,u1_struct_0(X32))|(~r2_hidden(X34,u1_struct_0(X33))|k1_funct_1(k4_tmap_1(X32,X33),X34)=X34)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.19/0.40  cnf(c_0_54, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.40  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_52])])).
% 0.19/0.40  cnf(c_0_56, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.40  cnf(c_0_57, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.40  cnf(c_0_58, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,X1),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)|u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)|~m1_pre_topc(X1,esk2_0)|~r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_60, negated_conjecture, (X1=k1_funct_1(esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_61, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_62, plain, (r1_tarski(X1,X2)|k1_funct_1(X1,esk1_2(X1,X2))!=k1_funct_1(X2,esk1_2(X1,X2))|~r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_55]), c_0_17])]), c_0_59])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_55]), c_0_57])).
% 0.19/0.40  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk3_0),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_49]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_66, plain, (k1_funct_1(X2,X1)=k1_funct_1(X3,X1)|~r2_hidden(X1,k1_relat_1(X2))|~r1_tarski(X2,X3)|~v1_relat_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)|~r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_50]), c_0_42]), c_0_51]), c_0_43])]), c_0_64])).
% 0.19/0.40  cnf(c_0_68, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(u1_struct_0(esk3_0),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_52]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)=k1_funct_1(X2,X1)|u1_struct_0(esk2_0)=k1_xboole_0|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,u1_struct_0(esk3_0))|~r1_tarski(k4_tmap_1(esk2_0,esk3_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_41]), c_0_42]), c_0_43])])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_41]), c_0_68])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))|r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)=k1_funct_1(esk4_0,X1)|u1_struct_0(esk2_0)=k1_xboole_0|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0))|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_49]), c_0_50]), c_0_51]), c_0_52])])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))|u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.40  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k1_relat_1(X1),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_49]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_76, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_74]), c_0_42]), c_0_50]), c_0_43]), c_0_51])])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(k1_relat_1(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_52]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_79, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|u1_struct_0(esk2_0)=k1_xboole_0|~r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_70])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_41]), c_0_78])).
% 0.19/0.40  fof(c_0_81, plain, ![X20, X21, X22, X23]:((~r2_funct_2(X20,X21,X22,X23)|X22=X23|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(X22!=X23|r2_funct_2(X20,X21,X22,X23)|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|~v1_funct_1(X23)|~v1_funct_2(X23,X20,X21)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.40  cnf(c_0_84, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.40  cnf(c_0_86, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_84])).
% 0.19/0.40  cnf(c_0_87, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_50]), c_0_36]), c_0_35])])).
% 0.19/0.40  cnf(c_0_89, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.40  cnf(c_0_90, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_87])).
% 0.19/0.40  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_35, c_0_88])).
% 0.19/0.40  cnf(c_0_92, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_36, c_0_88])).
% 0.19/0.40  cnf(c_0_93, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_89])).
% 0.19/0.40  cnf(c_0_94, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92])])).
% 0.19/0.40  cnf(c_0_95, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_93])).
% 0.19/0.40  cnf(c_0_96, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_91, c_0_94])).
% 0.19/0.40  cnf(c_0_97, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_94])).
% 0.19/0.40  cnf(c_0_98, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_24, c_0_88])).
% 0.19/0.40  cnf(c_0_99, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_25, c_0_88])).
% 0.19/0.40  cnf(c_0_100, negated_conjecture, (m1_subset_1(X1,k1_xboole_0)|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_54, c_0_88])).
% 0.19/0.40  cnf(c_0_101, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])).
% 0.19/0.40  cnf(c_0_102, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_98, c_0_94])).
% 0.19/0.40  cnf(c_0_103, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_94])).
% 0.19/0.40  cnf(c_0_104, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,X1),X2)=X2|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(X2,k1_xboole_0)|~r2_hidden(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_88]), c_0_18]), c_0_19])]), c_0_20])).
% 0.19/0.40  cnf(c_0_105, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(X1,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_100, c_0_94])).
% 0.19/0.40  cnf(c_0_106, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(esk4_0,X1),k1_xboole_0)|r1_tarski(esk4_0,X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_101]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_107, negated_conjecture, (k1_relat_1(k4_tmap_1(esk2_0,esk3_0))=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_102]), c_0_103])).
% 0.19/0.40  cnf(c_0_108, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_88]), c_0_100])).
% 0.19/0.40  cnf(c_0_109, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)=X1|esk4_0=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_94]), c_0_17])]), c_0_59]), c_0_105])).
% 0.19/0.40  cnf(c_0_110, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_42]), c_0_43]), c_0_52])])).
% 0.19/0.40  cnf(c_0_111, negated_conjecture, (k1_funct_1(esk4_0,X1)=X1|esk4_0=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_94])).
% 0.19/0.40  cnf(c_0_112, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(X1,esk4_0),k1_relat_1(X1))|r1_tarski(X1,esk4_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_101]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_113, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.19/0.40  cnf(c_0_114, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(esk4_0,k4_tmap_1(esk2_0,esk3_0))|esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_111, c_0_110])).
% 0.19/0.40  cnf(c_0_115, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_relat_1(X1),k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_101]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_116, negated_conjecture, (esk4_0=k1_xboole_0|r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_107]), c_0_42]), c_0_43]), c_0_52])])).
% 0.19/0.40  cnf(c_0_117, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))|~r1_tarski(k1_relat_1(esk4_0),k1_relat_1(k4_tmap_1(esk2_0,esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_113]), c_0_42]), c_0_50]), c_0_43]), c_0_51])]), c_0_114])).
% 0.19/0.40  cnf(c_0_118, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_relat_1(esk4_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_52]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_119, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)|esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_109, c_0_116])).
% 0.19/0.40  cnf(c_0_120, negated_conjecture, (k1_funct_1(esk4_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),esk4_0)|esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_111, c_0_116])).
% 0.19/0.40  cnf(c_0_121, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_xboole_0,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_101]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_122, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk4_0,k4_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_107]), c_0_118])).
% 0.19/0.40  cnf(c_0_123, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)|~r1_tarski(k1_relat_1(k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_119]), c_0_50]), c_0_42]), c_0_51]), c_0_43])]), c_0_120])).
% 0.19/0.40  cnf(c_0_124, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k1_xboole_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_52]), c_0_50]), c_0_51])])).
% 0.19/0.40  cnf(c_0_125, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0|~r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_122])).
% 0.19/0.40  cnf(c_0_126, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_107]), c_0_124])).
% 0.19/0.40  cnf(c_0_127, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_82, c_0_88])).
% 0.19/0.40  cnf(c_0_128, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=esk4_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.19/0.40  cnf(c_0_129, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=k1_xboole_0|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_98]), c_0_99])])).
% 0.19/0.40  cnf(c_0_130, negated_conjecture, (esk4_0=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_127, c_0_128])).
% 0.19/0.40  cnf(c_0_131, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_127, c_0_129])).
% 0.19/0.40  cnf(c_0_132, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_86]), c_0_50]), c_0_92]), c_0_91])])).
% 0.19/0.40  cnf(c_0_133, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_131, c_0_132])).
% 0.19/0.40  cnf(c_0_134, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_50, c_0_132])).
% 0.19/0.40  cnf(c_0_135, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_92, c_0_132])).
% 0.19/0.40  cnf(c_0_136, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),k1_xboole_0)))), inference(spm,[status(thm)],[c_0_98, c_0_129])).
% 0.19/0.40  cnf(c_0_137, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_86]), c_0_134]), c_0_135])]), c_0_136])).
% 0.19/0.40  cnf(c_0_138, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_98, c_0_137])).
% 0.19/0.40  cnf(c_0_139, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_99, c_0_137])).
% 0.19/0.40  cnf(c_0_140, negated_conjecture, (k1_relat_1(k4_tmap_1(esk2_0,esk3_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_138]), c_0_139])])).
% 0.19/0.40  cnf(c_0_141, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_132]), c_0_137])).
% 0.19/0.40  cnf(c_0_142, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_135, c_0_137])).
% 0.19/0.40  cnf(c_0_143, negated_conjecture, (m1_subset_1(X1,k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_100, c_0_137])).
% 0.19/0.40  cnf(c_0_144, negated_conjecture, (k1_funct_1(k1_xboole_0,X1)=X1|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_108, c_0_132])).
% 0.19/0.40  cnf(c_0_145, negated_conjecture, (r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),X1),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_140]), c_0_42]), c_0_43])])).
% 0.19/0.40  cnf(c_0_146, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_141]), c_0_142])])).
% 0.19/0.40  cnf(c_0_147, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_51, c_0_132])).
% 0.19/0.40  cnf(c_0_148, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)=X1|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_137]), c_0_17])]), c_0_59]), c_0_143])).
% 0.19/0.40  cnf(c_0_149, negated_conjecture, (k1_funct_1(k1_xboole_0,X1)=X1|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_144, c_0_137])).
% 0.19/0.40  cnf(c_0_150, negated_conjecture, (r2_hidden(esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_134]), c_0_147]), c_0_52])])).
% 0.19/0.40  cnf(c_0_151, negated_conjecture, (r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_relat_1(X1))|r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_140]), c_0_42]), c_0_43])])).
% 0.19/0.40  cnf(c_0_152, negated_conjecture, (r1_tarski(k4_tmap_1(esk2_0,esk3_0),X1)|k1_funct_1(X1,esk1_2(k4_tmap_1(esk2_0,esk3_0),X1))!=esk1_2(k4_tmap_1(esk2_0,esk3_0),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_xboole_0,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_148]), c_0_42]), c_0_43]), c_0_140])]), c_0_145])).
% 0.19/0.40  cnf(c_0_153, negated_conjecture, (k1_funct_1(k1_xboole_0,esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0))=esk1_2(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)|r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_149, c_0_150])).
% 0.19/0.40  cnf(c_0_154, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)|r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_146]), c_0_134]), c_0_147]), c_0_52])])).
% 0.19/0.40  cnf(c_0_155, negated_conjecture, (r1_tarski(k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_134]), c_0_147]), c_0_146]), c_0_52])])).
% 0.19/0.40  cnf(c_0_156, negated_conjecture, (r1_tarski(X1,k4_tmap_1(esk2_0,esk3_0))|k1_funct_1(X1,esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)))!=esk1_2(X1,k4_tmap_1(esk2_0,esk3_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(esk1_2(X1,k4_tmap_1(esk2_0,esk3_0)),k1_xboole_0)|~r1_tarski(k1_relat_1(X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_148]), c_0_42]), c_0_43]), c_0_140])])).
% 0.19/0.40  cnf(c_0_157, negated_conjecture, (k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0)))=esk1_2(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))|r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_149, c_0_154])).
% 0.19/0.40  cnf(c_0_158, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_127, c_0_132])).
% 0.19/0.40  cnf(c_0_159, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=k1_xboole_0|~r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_76, c_0_155])).
% 0.19/0.40  cnf(c_0_160, negated_conjecture, (r1_tarski(k1_xboole_0,k4_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156, c_0_154]), c_0_134]), c_0_147]), c_0_146]), c_0_52])]), c_0_157])).
% 0.19/0.40  cnf(c_0_161, negated_conjecture, (~r2_funct_2(k1_xboole_0,k1_xboole_0,k4_tmap_1(esk2_0,esk3_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_158, c_0_137])).
% 0.19/0.40  cnf(c_0_162, negated_conjecture, (k4_tmap_1(esk2_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_160])])).
% 0.19/0.40  cnf(c_0_163, negated_conjecture, (~r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_161, c_0_162])).
% 0.19/0.40  cnf(c_0_164, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_86]), c_0_134]), c_0_142]), c_0_141])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 165
% 0.19/0.40  # Proof object clause steps            : 140
% 0.19/0.40  # Proof object formula steps           : 25
% 0.19/0.40  # Proof object conjectures             : 119
% 0.19/0.40  # Proof object clause conjectures      : 116
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 29
% 0.19/0.40  # Proof object initial formulas used   : 12
% 0.19/0.40  # Proof object generating inferences   : 85
% 0.19/0.40  # Proof object simplifying inferences  : 220
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 12
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 34
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 34
% 0.19/0.40  # Processed clauses                    : 382
% 0.19/0.40  # ...of these trivial                  : 1
% 0.19/0.40  # ...subsumed                          : 96
% 0.19/0.40  # ...remaining for further processing  : 285
% 0.19/0.40  # Other redundant clauses eliminated   : 8
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 32
% 0.19/0.40  # Backward-rewritten                   : 144
% 0.19/0.40  # Generated clauses                    : 507
% 0.19/0.40  # ...of the previous two non-trivial   : 444
% 0.19/0.40  # Contextual simplify-reflections      : 21
% 0.19/0.40  # Paramodulations                      : 499
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 9
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 69
% 0.19/0.40  #    Positive orientable unit clauses  : 15
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 3
% 0.19/0.40  #    Non-unit-clauses                  : 51
% 0.19/0.40  # Current number of unprocessed clauses: 65
% 0.19/0.40  # ...number of literals in the above   : 537
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 209
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 3968
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1023
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 146
% 0.19/0.40  # Unit Clause-clause subsumption calls : 75
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 10
% 0.19/0.40  # BW rewrite match successes           : 9
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 17646
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.061 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.067 s
% 0.19/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
